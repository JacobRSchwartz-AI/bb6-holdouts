import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro, formatConfig } from '../src/macro.mjs';

// M3 build 4: the finale. Seeds the O-pay crisis at ν† = 3·2^279 (cascade
// state: left a e f f O, len 210) and runs long with samples. The machine's
// observed response is a wholesale tail re-spell e→a; this watches what
// regime follows.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const O = 10n, E = 14n, A = 11n, F = 15n;
const GLYPH = [10, 14, 11, 15];

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
const nu0 = 3n * (1n << 279n) - 12n;
const LEFT = [[A, 1n], [E, 1n], [F, 2n], [O, 1n]];
const LEN = 210;
const zone = Array.from({ length: LEN }, (_, j) => [cellGlyph(LEN - 1 - j, nu0), 1n]);
const cfg = coalesce([...LEFT, ...zone, [F, 1n], [E, nu0 - 2n], [O, 1n]]);

const res = runMacro(m, 4, {
  maxOps: 4e7, macro,
  init: { left: cfg.map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n },
  sampleEvery: 2e6,
  onSample: (s) => {
    const all = [...s.left, ...s.right];
    const giant = all.reduce((m2, r) => (r[1] > m2[1] ? r : m2), all[0]);
    const leftOfGiant = s.left.filter((r) => r[1] < 1n << 60n);
    const blocks = leftOfGiant.reduce((a, [, c]) => a + c, 0n);
    console.log(`ops=${s.ops}  left-structure: runs=${leftOfGiant.length} blocks=${blocks}  giant=${giant[1].toString().slice(-9)}  ${formatConfig(s.left, s.right, s.facing, s.q, 4, 6)}`);
  },
});
console.log(`\nstatus=${res.status}${res.cert ? `  CERT=${res.cert}` : ''}  ops=${res.ops}`);
console.log(`final: ${res.config}`);
