import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// M3.5 step 3: winter #2 (P-2026-08-14-l). Seed SPELL₃ at v = 2^283 − 12 —
// the carry at v = 2^283 needs cell 213, which does not exist. Observe the
// crisis sweep and the post-crisis structure; then (if a melt) probe the
// NEW spelling the same way. Also mode 'w3plus' to iterate later winters.
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
const coalesce = (runs) => {
  const out = [];
  for (const [b, c] of runs) {
    if (c === 0n) continue;
    if (out.length && out[out.length - 1][0] === b) out[out.length - 1][1] += c;
    else out.push([b, c]);
  }
  return out;
};

const N = BigInt(process.argv[2] ?? '0');   // winter index: epoch = 3·2^279 + N·2^283
const EPOCH = 3n * (1n << 279n) + N * (1n << 283n);
const LEN3 = 213;
const V0 = (1n << 283n) - 12n;
const nuStart = EPOCH + V0;
const crisisNu = EPOCH + (1n << 283n);
const runs = coalesce([
  [A, 2n],
  ...Array.from({ length: LEN3 }, (_, j) => [cellGlyph(LEN3 - 1 - j, V0), 1n]),
  [F, 1n], [E, nuStart - 2n], [O, 1n],
]);
console.log(`seed ν = EPOCH + 2^283 − 12; crisis sweep expected into ν = 19·2^279`);
console.log(`seed left edge: ${fmt(runs.slice(0, 8))}`);

const trail = (x) => { let t = 0n; while ((x & 1n) === 1n) { x >>= 1n; t++; } return t; };
let prevSteps = null, prevNu = null, shown = 0;
const res = runMacro(m, 4, {
  maxOps: 60000, macro,
  init: { left: runs.map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n },
  onEdge: (s) => {
    if (s.ops === 1 || s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    const L = s.left;
    const gi = L.reduce((g, r, i) => (r[1] > L[g][1] ? i : g), 0);
    if (L[gi][1] < 1n << 60n) return;
    const nu = L[gi][1] + 2n;
    const nearCrisis = nu >= crisisNu - 3n && nu <= crisisNu + 6n;
    if (shown < 6 || nearCrisis) {
      let costNote = '';
      if (prevSteps !== null && prevNu !== null && nu === prevNu + 1n) {
        const t = trail(nu - 1n);
        const base = 16n * (nu - 1n) + 34n + 6n * t + (t % 2n === 0n ? 2n : 0n);
        costNote = `  dev=${s.steps - prevSteps - base}`;
      }
      console.log(`ν=EPOCH+2^283${nu >= crisisNu ? '+' + (nu - crisisNu) : '−' + (crisisNu - nu)}  left: ${fmt(L.slice(0, gi))}${costNote}`);
      shown++;
    }
    prevSteps = s.steps; prevNu = nu;
  },
});
console.log(`status: ${res.status}${res.cert ? '  CERT=' + res.cert : ''}`);
if (res.status === 'halt') console.log('*** HALT ***');
console.log(`final: ${res.config}`);
