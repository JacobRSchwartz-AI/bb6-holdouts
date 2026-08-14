import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// Grade the P-2026-08-14-i blind test directly: seed SPELL(2^32 − 12) from
// the calendar state (era s=15, font a after the 2^30 respell) and cross the
// k=32 respell concretely. Reads off the respell sweep cost (candidates
// 1716 / 1720 / 1728) and cross-checks the post-collapse anchor against the
// j=32 chain's independently computed config.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };
const GLYPH = [10, 14, 11, 15];
const O = 10n, E = 14n, A = 11n, F = 15n;
const fmt = (rs) => rs.map(([b, c]) => `${NAME[Number(b)] ?? Number(b).toString(2)}^${c}`).join(' ');

function cellGlyph(i, nu) {
  if (i === 0) return 10n;
  const r = (i - 1) % 3;
  if (r === 0) {
    const s = i === 1 ? 0n : BigInt(4 * ((i - 4) / 3) + 4);
    return ((nu >> s) & 1n) === 1n ? 15n : 10n;
  }
  const mt = r === 1 ? (i - 2) / 3 : (i - 3) / 3;
  const s = BigInt(4 * mt + r);
  return BigInt(GLYPH[Number((nu >> s) & 3n)]);
}

// calendar state at ν = 2^32 − 12
let R = 202n, len = 5, font = E;
for (let k = 5n; k <= 32n; k++) {
  const p = 1n << k;
  const r = k % 4n;
  const evs = [];
  if (r === 0n) evs.push([p, 'respell']);
  if (r === 1n) { evs.push([p, 'pay']); evs.push([3n * p, 'pay']); }
  if (r === 2n) { evs.push([p, 'respell']); evs.push([3n * p, 'pay']); evs.push([5n * p, 'borrow']); }
  if (r === 3n) evs.push([3n * p, 'pay']);
  for (const [nu, type] of evs) {
    if (nu <= 34n || nu >= (1n << 32n)) continue;
    if (type === 'pay') { len++; R--; }
    else if (type === 'borrow') { len--; R++; }
    else font = font === E ? A : E;
  }
}
console.log(`state entering 2^32: R=${R} len=${len} font=${NAME[Number(font)]} (chain says zone=25 post-respell)`);

const PRE15 = [[A, 1n], [O, 3n], [F, 2n], [A, 1n], [E, 1n]];   // s=15, observed
const nu0 = (1n << 32n) - 12n;
const runs = [];
const push = (b, c) => {
  if (c === 0n) return;
  if (runs.length && runs[runs.length - 1][0] === b) runs[runs.length - 1][1] += c;
  else runs.push([b, c]);
};
for (const [b, c] of PRE15) push(b, c);
push(font, R);
for (let i = len - 1; i >= 0; i--) push(cellGlyph(i, nu0), 1n);
push(F, 1n); push(E, nu0 - 2n); push(O, 1n);
console.log(`seed: ${fmt(runs.slice(0, 8))} … ${fmt(runs.slice(-3))}`);

let prevSteps = null, prevNu = null;
const res = runMacro(m, 4, {
  maxOps: 20000, macro,
  init: { left: runs.map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n },
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    if (s.ops === 1) return;
    const L = s.left;
    const nu = L[L.length - 2][1] + 2n;
    if (prevNu !== null && nu >= (1n << 32n) - 2n && nu <= (1n << 32n) + 2n) {
      const cost = s.steps - prevSteps;
      const dev = cost - 16n * (nu - 1n);
      console.log(`sweep into ν=${nu}${nu === 1n << 32n ? ' (THE RESPELL)' : ''}: cost−16(ν−1) = ${dev}`);
      if (nu === 1n << 32n) {
        console.log(`  → respell surcharge over 1680: c(4) = ${dev - 1680n}`);
        console.log(`  post-collapse anchor: ${fmt(L.slice(0, 8))} …`);
        const chain = 'a^1 O^2 e^1 O^4';
        console.log(`  chain's j=32 preamble:  ${chain}  |  seed harness sees: ${fmt(L.slice(0, 4))}`);
      }
    }
    prevSteps = s.steps; prevNu = nu;
  },
});
console.log(`status: ${res.status}`);
