// Tiny stack VM (make.fun tiny stack ISA v1). Reads /input/<id>/program.bin +
// input.bin, writes /output/<id>/stdout.bin + exit.txt. Node 22, stdlib only,
// deterministic: no clock, no env-dependent behaviour.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
// Immediate lengths; 0 for opcodes without one (and for unknown opcodes,
// which the switch below traps as 5 after this same length check).
const IMM = new Uint8Array(256);
IMM[0x01] = 1; IMM[0x02] = 4;
IMM[0x30] = 2; IMM[0x31] = 2; IMM[0x32] = 2; IMM[0x33] = 2;

function run(prog: Buffer, input: Buffer): { out: Buffer; code: number } {
  const mem = new Int32Array(256);
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, pc = 0, ip = 0, steps = 0, n = 0;
  const len = prog.length;
  let code = 0;
  outer: while (true) {
    if (steps >= 1000000) { code = 10; break; } // step limit
    if (pc < 0 || pc >= len) { code = 9; break; } // pc outside program
    const op = prog[pc];
    if (pc + 1 + IMM[op] > len) { code = 9; break; } // immediate cut off
    steps++;
    switch (op) {
      case 0x00: code = 0; break outer; // HALT
      case 0x01: // PUSH8, sign-extended
        if (sp >= 256) { code = 3; break outer; }
        { const b = prog[pc + 1]; st[sp++] = b >= 128 ? b - 256 : b; }
        pc += 2; break;
      case 0x02: // PUSH32, signed LE
        if (sp >= 256) { code = 3; break outer; }
        st[sp++] = prog[pc + 1] | (prog[pc + 2] << 8) | (prog[pc + 3] << 16) | (prog[pc + 4] << 24);
        pc += 5; break;
      case 0x03: if (sp < 1) { code = 2; break outer; } sp--; pc++; break; // POP
      case 0x04: // DUP
        if (sp < 1) { code = 2; break outer; }
        if (sp >= 256) { code = 3; break outer; }
        st[sp] = st[sp - 1]; sp++; pc++; break;
      case 0x05: // SWAP
        if (sp < 2) { code = 2; break outer; }
        { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; }
        pc++; break;
      case 0x06: // OVER
        if (sp < 2) { code = 2; break outer; }
        if (sp >= 256) { code = 3; break outer; }
        st[sp] = st[sp - 2]; sp++; pc++; break;
      case 0x07: // ROT (a b c -- b c a)
        if (sp < 3) { code = 2; break outer; }
        { const t = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = t; }
        pc++; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (sp < 2) { code = 2; break outer; }
        const b = st[--sp], a = st[sp - 1];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) { code = 4; break outer; } r = (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) { code = 4; break outer; } r = (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) { code = 4; break outer; } r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) { code = 4; break outer; } r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        st[sp - 1] = r;
        pc++; break;
      }
      case 0x17: if (sp < 1) { code = 2; break outer; } st[sp - 1] = (-st[sp - 1]) | 0; pc++; break; // NEG
      case 0x1b: if (sp < 1) { code = 2; break outer; } st[sp - 1] = ~st[sp - 1]; pc++; break; // NOT
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset
        let off = prog[pc + 1] | (prog[pc + 2] << 8);
        if (off >= 32768) off -= 65536;
        if (op === 0x30) { pc = pc + 3 + off; break; }
        if (sp < 1) { code = 2; break outer; }
        const v = st[--sp];
        pc = (op === 0x31 ? v === 0 : v !== 0) ? pc + 3 + off : pc + 3;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit absolute target
        if (csp >= 64) { code = 7; break outer; }
        cs[csp++] = pc + 3;
        pc = prog[pc + 1] | (prog[pc + 2] << 8);
        break;
      case 0x34: if (csp === 0) { code = 8; break outer; } pc = cs[--csp]; break; // RET
      case 0x40: // LOAD
        if (sp < 1) { code = 2; break outer; }
        { const a = st[sp - 1];
          if (a < 0 || a > 255) { code = 6; break outer; }
          st[sp - 1] = mem[a]; }
        pc++; break;
      case 0x41: // STORE (v addr --)
        if (sp < 2) { code = 2; break outer; }
        { const a = st[--sp], v = st[--sp];
          if (a < 0 || a > 255) { code = 6; break outer; }
          mem[a] = v; }
        pc++; break;
      case 0x50: { // PRINT decimal ASCII
        if (sp < 1) { code = 2; break outer; }
        const s = String(st[--sp]);
        if (n + s.length > 65536) { code = 11; break outer; }
        for (let i = 0; i < s.length; i++) out[n++] = s.charCodeAt(i);
        pc++; break;
      }
      case 0x51: // PUTC
        if (sp < 1) { code = 2; break outer; }
        if (n + 1 > 65536) { code = 11; break outer; }
        out[n++] = st[--sp] & 255;
        pc++; break;
      case 0x52: // IN
        if (sp >= 256) { code = 3; break outer; }
        st[sp++] = ip < input.length ? input[ip++] : -1;
        pc++; break;
      case 0x53: // EXIT, low byte
        if (sp < 1) { code = 2; break outer; }
        code = st[--sp] & 255; break outer;
      default: code = 5; break outer; // unknown opcode
    }
  }
  return { out: Buffer.from(out.subarray(0, n)), code };
}

for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  const progPath = join(dir, 'program.bin');
  if (!existsSync(progPath)) continue;
  const prog = readFileSync(progPath);
  const inPath = join(dir, 'input.bin');
  const input = existsSync(inPath) ? readFileSync(inPath) : Buffer.alloc(0);
  const { out, code } = run(prog, input);
  const od = join(O, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), out);
  writeFileSync(join(od, 'exit.txt'), String(code) + '\n');
}
