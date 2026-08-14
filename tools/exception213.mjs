import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// P-2026-08-15-p run 1: SPELL3 seeded at v = 2^282 - 12 (boundary a a),
// cross v = 2^282 - 1. Predict: inner a -> f, machine continues re-based.
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
const V0 = (1n << 282n) - 12n;
const nuStart = EPOCH + V0;
const crossNu = EPOCH + (1n << 282n);
const runs = coalesce([
  [A, 2n],
  ...Array.from({ length: LEN3 }, (_, j) => [cellGlyph(LEN3 - 1 - j, V0), 1n]),
  [F, 1n], [E, nuStart - 2n], [O, 1n],
]);
console.log(`seed v = 2^282 - 12; watch the crossing at v = 2^282`);
let prevNu = null, shown = 0;
const res = runMacro(m, 4, {
  maxOps: 60000, macro,
  init: { left: runs.map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n },
  onEdge: (s) => {
    if (s.ops === 1 || s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    const L = s.left;
    const gi = L.reduce((g, r, i) => (r[1] > L[g][1] ? i : g), 0);
    if (L[gi][1] < 1n << 60n) return;
    const nu = L[gi][1] + 2n;
    const near = nu >= crossNu - 3n && nu <= crossNu + 8n;
    if (shown < 4 || near) {
      console.log(`v=2^282${nu >= crossNu ? '+' + (nu - crossNu) : '-' + (crossNu - nu)}  left: ${fmt(L.slice(0, Math.min(gi, 12)))}${gi > 12 ? ' ...' : ''}`);
      shown++;
    }
    prevNu = nu;
  },
});
console.log(`status: ${res.status}${res.status === 'halt' ? '  *** HALT ***' : ''}`);
