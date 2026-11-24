// Tiny stack VM: runs every program in MAKEFUN_INPUT_DIR and writes its
// stdout.bin + exit.txt to MAKEFUN_OUTPUT_DIR. Follows the tiny stack ISA:
// 32-bit wrapping values, 256-slot data stack, 64-deep call stack, 256
// memory words, 1,000,000 steps, 65,536 output bytes, traps 2..11.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode: [immediate bytes, values popped, values pushed].
// Only the opcodes the ISA defines are listed; anything else is trap 5.
const META = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1], 0x20: [0, 2, 1],
  0x21: [0, 2, 1], 0x22: [0, 2, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};

function run(prog, input) {
  const st = new Int32Array(256); // data stack
  const ret = new Int32Array(64); // return addresses
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  const enc = new TextEncoder();
  let sp = 0, rp = 0, pc = 0, steps = 0, ip = 0, len = 0;
  const end = (code) => ({ out: out.slice(0, len), code });
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= prog.length) return end(9);
    const meta = META[prog[pc]];
    if (!meta) return end(5);
    if (pc + meta[0] >= prog.length) return end(9);
    steps++;
    const nxt = pc + 1 + meta[0];
    if (sp < meta[1]) return end(2);
    if (sp - meta[1] + meta[2] > 256) return end(3);
    pc = nxt;
    const op = prog[nxt - 1 - meta[0]];
    if (op === 0x00) return end(0);
    if (op === 0x01) { st[sp++] = (prog[nxt - 1] << 24) >> 24; continue; }
    if (op === 0x02) {
      st[sp++] = prog[nxt - 4] | (prog[nxt - 3] << 8) | (prog[nxt - 2] << 16) | (prog[nxt - 1] << 24);
      continue;
    }
    if (op === 0x03) { sp--; continue; }
    if (op === 0x04) { st[sp] = st[sp - 1]; sp++; continue; }
    if (op === 0x05) { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; continue; }
    if (op === 0x06) { st[sp] = st[sp - 2]; sp++; continue; }
    if (op === 0x07) {
      const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a;
      continue;
    }
    if (op === 0x17) { st[sp - 1] = (-st[sp - 1]) | 0; continue; }
    if (op === 0x1b) { st[sp - 1] = ~st[sp - 1]; continue; }
    if (op >= 0x10 && op <= 0x22) {
      const b = st[sp - 1], a = st[sp - 2];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) {
        if (b === 0) return end(4);
        r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
      } else if (op === 0x14) {
        if (b === 0) return end(4);
        r = b === -1 ? 0 : (a % b) | 0;
      } else if (op === 0x15) {
        if (b === 0) return end(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      } else if (op === 0x16) {
        if (b === 0) return end(4);
        r = ((a >>> 0) % (b >>> 0)) | 0;
      } else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 2; st[sp++] = r;
      continue;
    }
    if (op === 0x30 || op === 0x31 || op === 0x32) {
      const off = ((prog[nxt - 2] | (prog[nxt - 1] << 8)) << 16) >> 16;
      let go = op === 0x30;
      if (!go) { const v = st[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
      if (go) pc = nxt + off;
      continue;
    }
    if (op === 0x33) {
      if (rp === 64) return end(7);
      ret[rp++] = nxt;
      pc = prog[nxt - 2] | (prog[nxt - 1] << 8);
      continue;
    }
    if (op === 0x34) {
      if (rp === 0) return end(8);
      pc = ret[--rp];
      continue;
    }
    if (op === 0x40) {
      const a = st[sp - 1];
      if (a < 0 || a >= 256) return end(6);
      st[sp - 1] = mem[a];
      continue;
    }
    if (op === 0x41) {
      const a = st[sp - 1], v = st[sp - 2];
      if (a < 0 || a >= 256) return end(6);
      sp -= 2; mem[a] = v;
      continue;
    }
    if (op === 0x50) {
      const bytes = enc.encode(String(st[sp - 1]));
      if (len + bytes.length > 65536) return end(11);
      sp--; out.set(bytes, len); len += bytes.length;
      continue;
    }
    if (op === 0x51) {
      if (len + 1 > 65536) return end(11);
      out[len++] = st[--sp] & 255;
      continue;
    }
    if (op === 0x52) { st[sp++] = ip < input.length ? input[ip++] : -1; continue; }
    return end(st[--sp] & 255); // EXIT (0x53)
  }
}

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN).sort()) {
  const dir = join(IN, id);
  let prog, input;
  try { prog = readFileSync(join(dir, 'program.bin')); } catch { prog = Buffer.alloc(0); }
  try { input = readFileSync(join(dir, 'input.bin')); } catch { input = Buffer.alloc(0); }
  const r = run(new Uint8Array(prog), new Uint8Array(input));
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), r.out);
  writeFileSync(join(OUT, id, 'exit.txt'), r.code + '\n');
}
