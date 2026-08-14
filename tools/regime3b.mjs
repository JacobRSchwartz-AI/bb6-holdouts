import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// M3.5 step 1b: regime-3 anchors in full. Same seed as regime3.mjs; at each
// C>-right-edge anchor, record the complete structure left of the giant run
// and the exact sweep cost deviation from the old clock base 16ν+34+6t+2[t even].
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
const nu0 = 3n * (1n << 279n) - 12n;
const LEFT = [[A, 1n], [E, 1n], [F, 2n], [O, 1n]];
const LEN = 210;
const runs = [];
const push = (b, c) => {
  if (c === 0n) return;
  if (runs.length && runs[runs.length - 1][0] === b) runs[runs.length - 1][1] += c;
  else runs.push([b, c]);
};
for (const [b, c] of LEFT) push(b, c);
for (let i = LEN - 1; i >= 0; i--) push(cellGlyph(i, nu0), 1n);
push(F, 1n); push(E, nu0 - 2n); push(O, 1n);

const trail = (x) => { let t = 0n; while ((x & 1n) === 1n) { x >>= 1n; t++; } return t; };
let prevSteps = null, prevNu = null, shown = 0, checked = 0, clockOk = 0;
const devCensus = new Map();
let latticeOk = 0, latticeBad = [];
const res = runMacro(m, 4, {
  maxOps: 300000, macro,
  init: { left: runs.map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n },
  onEdge: (s) => {
    if (s.ops === 1 || s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    const L = s.left;
    const gi = L.reduce((g, r, i) => (r[1] > L[g][1] ? i : g), 0);
    if (L[gi][1] < 1n << 60n) return;
    const nu = L[gi][1] + 2n;
    const leftRuns = L.slice(0, gi);
    const between = L.slice(gi + 1);
    // zone check: parse leftRuns as zoo + zone(nu, len) for the largest len that fits the lattice
    if (shown < 14 || (prevNu !== null && trail(nu - 1n) > 8n)) {
      console.log(`ν=…${nu.toString().slice(-10)}  left: ${fmt(leftRuns)}  | giant e^${nu - 2n === L[gi][1] ? 'ν−2' : '≠ν−2!'} | ${fmt(between)}`);
      shown++;
    }
    if (prevSteps !== null && prevNu !== null && nu === prevNu + 1n) {
      checked++;
      const t = trail(nu - 1n);
      const base = 16n * (nu - 1n) + 34n + 6n * t + (t % 2n === 0n ? 2n : 0n);
      const dev = s.steps - prevSteps - base;
      if (!devCensus.has(dev.toString())) devCensus.set(dev.toString(), { n: 0, ts: new Set() });
      const c = devCensus.get(dev.toString());
      c.n++; c.ts.add(Number(t));
      if (dev === 0n) clockOk++;
    }
    // lattice check on the low zone: expand leftRuns' tail into cells and compare glyphs for cells 0..25
    const cells = [];
    for (let i = leftRuns.length - 1; i >= 0 && cells.length < 30; i--) {
      const [b, c] = leftRuns[i];
      const reps = c < 30n ? Number(c) : 30;
      for (let r = 0; r < reps && cells.length < 30; r++) cells.push(BigInt(b));
    }
    let ok = true;
    for (let i = 1; i <= 25; i++) if (cells[i] !== cellGlyph(i, nu)) { ok = false; break; }
    if (ok) latticeOk++;
    else if (latticeBad.length < 5) latticeBad.push({ nu: nu.toString().slice(-8), got: cells.slice(0, 12).map((b) => NAME[Number(b)]).join(''), want: Array.from({ length: 12 }, (_, i) => NAME[Number(cellGlyph(i, nu))]).join('') });
    prevSteps = s.steps; prevNu = nu;
  },
});
console.log(`\nsweeps checked: ${checked}; old clock base EXACT: ${clockOk} (${(100 * clockOk / checked).toFixed(2)}%)`);
console.log('deviation census (dev: count, trailing-ones values seen):');
for (const [dev, c] of [...devCensus.entries()].sort((a, b) => b[1].n - a[1].n).slice(0, 12)) {
  console.log(`  dev=${dev}: ×${c.n}  t∈{${[...c.ts].sort((x, y) => x - y).slice(0, 8).join(',')}}`);
}
console.log(`\nlow-zone lattice (cells 1..25) exact: ${latticeOk}/${checked + 1}`);
for (const b of latticeBad) console.log(`  ν=…${b.nu}: got ${b.got} want ${b.want} (cells 0..11, right to left)`);
