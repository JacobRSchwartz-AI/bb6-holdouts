import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// P-2026-08-15-p run 2: seed the corrected (post-exception cascade)
// structure at v = 2^283 - 2, scaled from the toy's iterate-126 string
// fOOfffffa -> [a, f^212, O, O, f-sep]. Predict: HALT within ~2 sweeps.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };
const O = 10n, E = 14n, A = 11n, F = 15n;
const fmt = (rs) => rs.map(([b, c]) => `${NAME[Number(b)] ?? Number(b).toString(2)}^${c}`).join(' ');
const EPOCH = 3n * (1n << 279n);
const v = (1n << 283n) - 2n;
const nu = EPOCH + v;
const runs = [[A, 1n], [F, 212n], [O, 2n], [F, 1n], [E, nu - 2n], [O, 1n]];
let shown = 0;
const res = runMacro(m, 4, {
  maxOps: 60000, macro,
  init: { left: runs.map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n },
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    const L = s.left;
    const gi = L.reduce((g, r, i) => (r[1] > L[g][1] ? i : g), 0);
    if (L[gi][1] < 1n << 60n) return;
    if (shown < 8) { console.log(`anchor: left ${fmt(L.slice(0, Math.min(gi, 10)))} | e^giant | ${fmt(L.slice(gi + 1))}`); shown++; }
  },
});
console.log(`status: ${res.status}${res.status === 'halt' ? '  *** THE ODOMETER HALTS ***' : ''}`);
console.log(`final config (truncated): ${String(res.config).slice(0, 200)}`);
