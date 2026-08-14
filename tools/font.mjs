import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// Font-overlay fit (P-2026-08-14-a): for each settled bit cell (index 3m+4)
// and each calendar era, which glyph spells value 0 ({O,a}) and value 1
// ({e,f})? Window cells are value-determined; bit cells are the only
// spelling freedom — this fit pins it, completing SPELL(ν).
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const SYM = { 10: 0n, 14: 1n, 11: 2n, 15: 3n };
const NAME = ['O', 'e', 'a', 'f'];

const anchors = [];
runMacro(m, 4, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    anchors.push(s.left.map(([b, c]) => [b, c]));
  },
});

const EVENTS = [64n, 96n, 192n, 256n, 320n, 384n, 512n, 1024n, 1536n, 3072n,
  4096n, 5120n, 6144n, 8192n, 16384n, 24576n, 49152n, 65536n, 81920n,
  98304n, 131072n, 262144n];
const eraOf = (nu) => {
  let e = 0;
  while (e < EVENTS.length && nu >= EVENTS[e]) e++;
  return e;
};
const eraName = (e) => `[${e === 0 ? 34n : EVENTS[e - 1]},${e < EVENTS.length ? EVENTS[e] : '…'})`;
const factored = (x) => { let k = 0n, o = x; while (o % 2n === 0n && o > 0n) { o /= 2n; k++; } return `${o}·2^${k}`; };

const rows = [];
for (const L of anchors) {
  if (L.length < 6) continue;
  const nu = L[L.length - 2][1] + 2n;
  if (nu < 34n) continue;
  const digits = [];
  let merged = false, resFont = '?';
  for (let i = L.length - 4; i >= 0; i--) {
    const [b, c] = L[i];
    if (SYM[b] === undefined || c >= 60n) { resFont = NAME[Number(SYM[b] ?? -1n)] ?? '?'; break; }
    for (let r = 0n; r < c; r++) digits.push(SYM[b]);
  }
  const expect = nu.toString(2).length - 2;
  merged = digits.length !== expect;
  rows.push({ nu, digits, merged, resFont });
}

// stats: `${cell}|${era}|${bit}` -> Map(glyph -> {n, first, last})
const stats = new Map();
const oddGlyphNus = [];   // every a-spelling and every off-parity 1-font, for inspection
for (const r of rows) {
  const e = eraOf(r.nu);
  for (let i = 4; i < r.digits.length; i++) {
    if ((i - 4) % 3 !== 0) continue;   // bit cells only
    const mTier = (i - 4) / 3;
    const bit = (r.nu >> BigInt(4 * mTier + 4)) & 1n;
    const g = NAME[Number(r.digits[i])];
    const key = `${String(i).padStart(2)}|${String(e).padStart(2)}|${bit}`;
    if (!stats.has(key)) stats.set(key, new Map());
    const gm = stats.get(key);
    if (!gm.has(g)) gm.set(g, { n: 0, first: r.nu, last: r.nu });
    const rec = gm.get(g);
    rec.n++; rec.last = r.nu;
    if (g === 'a' && oddGlyphNus.length < 400) oddGlyphNus.push({ i, nu: r.nu, merged: r.merged, resFont: r.resFont });
  }
}

console.log('bit-cell glyph usage per (cell, era, value):  [glyph n first..last]');
let lastCell = '';
for (const key of [...stats.keys()].sort()) {
  const [cell, era, bit] = key.split('|');
  if (cell !== lastCell) { console.log(`\ncell ${cell.trim()} (bit ${4 * ((Number(cell) - 4) / 3) + 4}):`); lastCell = cell; }
  const gm = stats.get(key);
  const parts = [...gm.entries()].map(([g, r]) => `${g}×${r.n} (${factored(r.first)}..${factored(r.last)})`);
  const mixed = gm.size > 1 ? '  <-- MIXED' : '';
  console.log(`  era ${eraName(Number(era))} val=${bit}: ${parts.join('  ')}${mixed}`);
}

console.log(`\n${oddGlyphNus.length} a-spellings at bit cells (first 60):`);
for (const o of oddGlyphNus.slice(0, 60)) {
  console.log(`  cell ${o.i} ν=${String(o.nu).padStart(7)} = ${factored(o.nu).padEnd(9)} merged=${o.merged ? 'Y' : 'n'} res=${o.resFont}`);
}
