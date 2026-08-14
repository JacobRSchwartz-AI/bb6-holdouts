import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// M3.5 step 2: SPELL₃ jump-validation. Hypothesis (from regime3b):
//   SPELL₃(ν) = a² · vzone(v, 213) · f¹ · e^(ν−2) · O¹,  v = ν − 3·2^279
// (zone re-based at the crisis; a² = compressed epoch memory; tail holds ν).
// Seed at jumped v values — small, medium (2^40), large (2^100, 2^200),
// near-collapse (v = 2^212−8: full-depth carry inside the v-zone) — run
// ~200 sweeps each, check every anchor against SPELL₃ and the clock.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };
const GLYPH = [10, 14, 11, 15];
const O = 10n, E = 14n, A = 11n, F = 15n;
const fmt = (rs) => rs.map(([b, c]) => `${NAME[Number(b)] ?? Number(b).toString(2)}^${c}`).join(' ');
const EPOCH = 3n * (1n << 279n);
const LEN3 = 213;

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
const coalesce = (runs) => {
  const out = [];
  for (const [b, c] of runs) {
    if (c === 0n) continue;
    if (out.length && out[out.length - 1][0] === b) out[out.length - 1][1] += c;
    else out.push([b, c]);
  }
  return out;
};
const spell3 = (nu) => {
  const v = nu - EPOCH;
  const runs = [[A, 2n]];
  for (let i = LEN3 - 1; i >= 0; i--) runs.push([cellGlyph(i, v), 1n]);
  runs.push([F, 1n], [E, nu - 2n], [O, 1n]);
  return coalesce(runs);
};
const trail = (x) => { let t = 0n; while ((x & 1n) === 1n) { x >>= 1n; t++; } return t; };
const runsEq = (a, b) => a.length === b.length && a.every(([x, c], i) => x === b[i][0] && c === b[i][1]);

const JUMPS = [
  ['v=64', 64n],
  ['v=2^40−8', (1n << 40n) - 8n],
  ['v=2^100−8', (1n << 100n) - 8n],
  ['v=2^200−8', (1n << 200n) - 8n],
  ['v=5·2^150−8', 5n * (1n << 150n) - 8n],
  ['v=2^212−8', (1n << 212n) - 8n],
];
for (const [label, v0] of JUMPS) {
  const nuStart = EPOCH + v0;
  const init = { left: spell3(nuStart).map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n };
  let checked = 0, ok = 0, clockOk = 0, firstBad = null, prevSteps = null, prevNu = null;
  const res = runMacro(m, 4, {
    maxOps: 8000, macro, init,
    onEdge: (s) => {
      if (s.ops === 1 || s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
      const L = s.left;
      const gi = L.reduce((g, r, i) => (r[1] > L[g][1] ? i : g), 0);
      if (L[gi][1] < 1n << 60n) return;
      const nu = L[gi][1] + 2n;
      checked++;
      const want = spell3(nu);
      const got = L.map(([b, c]) => [BigInt(b), c]);
      if (runsEq(got, want)) ok++;
      else if (!firstBad) firstBad = { nu, got: fmt(got.slice(0, 8)), want: fmt(want.slice(0, 8)) };
      if (prevNu !== null && nu === prevNu + 1n) {
        const t = trail(nu - 1n);
        const base = 16n * (nu - 1n) + 34n + 6n * t + (t % 2n === 0n ? 2n : 0n);
        if (s.steps - prevSteps === base) clockOk++;
      }
      prevNu = nu; prevSteps = s.steps;
    },
  });
  console.log(`${label.padEnd(14)} anchors=${checked}  SPELL₃ exact=${ok}  clock exact=${clockOk}`);
  if (firstBad) console.log(`   first mismatch ν=…${firstBad.nu.toString().slice(-8)}\n     got : ${firstBad.got}\n     want: ${firstBad.want}`);
}
