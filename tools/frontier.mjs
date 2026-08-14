import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// Frontier fit: for each zone cell index i and each calendar era (intervals
// between the 22 zone-size/font events), fit the cell's exact law from
// {window@2^s, bit@2^s (font {O,a}=0,{e,f}=1), constant}. Settled cells
// should show one law from birth+1 onward; the frontier cells' era-by-era
// phase sequence is the object we need for the SPELL(ν) invariant.
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

// calendar events (from tools/cells.mjs) as era boundaries
const EVENTS = [64n, 96n, 192n, 256n, 320n, 384n, 512n, 1024n, 1536n, 3072n,
  4096n, 5120n, 6144n, 8192n, 16384n, 24576n, 49152n, 65536n, 81920n,
  98304n, 131072n, 262144n];

const rows = [];
for (const L of anchors) {
  if (L.length < 6) continue;
  const nu = L[L.length - 2][1] + 2n;
  if (nu < 34n) continue;
  const digits = [];
  for (let i = L.length - 4; i >= 0; i--) {
    const [b, c] = L[i];
    if (SYM[b] === undefined || c >= 60n) break;
    for (let r = 0n; r < c; r++) digits.push(SYM[b]);
  }
  rows.push({ nu, digits });
}

const eraOf = (nu) => {
  let e = 0;
  while (e < EVENTS.length && nu >= EVENTS[e]) e++;
  return e;   // era e = [EVENTS[e-1], EVENTS[e])
};
const eraName = (e) => `[${e === 0 ? 34n : EVENTS[e - 1]},${e < EVENTS.length ? EVENTS[e] : '…'})`;

const bitVal = (s) => (s === 0n || s === 2n ? 0n : 1n);

// bucket samples per (cell, era)
const buckets = new Map();
for (const r of rows) {
  const e = eraOf(r.nu);
  for (let i = 4; i < Math.min(r.digits.length, 15); i++) {
    const key = `${i}|${e}`;
    if (!buckets.has(key)) buckets.set(key, []);
    const b = buckets.get(key);
    if (b.length < 60000) b.push({ nu: r.nu, s: r.digits[i] });
  }
}

function fitLaws(samples, i) {
  const laws = [];
  const allEq = samples.every((x) => x.s === samples[0].s);
  if (allEq) laws.push(`const ${NAME[Number(samples[0].s)]}`);
  for (let s = Math.max(0, i - 4); s <= i + 3; s++) {
    if (samples.every((x) => x.s === ((x.nu >> BigInt(s)) & 3n))) laws.push(`win@2^${s}`);
  }
  for (let s = Math.max(0, i - 3); s <= i + 4; s++) {
    if (samples.every((x) => bitVal(x.s) === ((x.nu >> BigInt(s)) & 1n))) laws.push(`bit@2^${s}`);
  }
  return laws;
}

for (let i = 4; i <= 14; i++) {
  const parts = [];
  for (let e = 0; e <= EVENTS.length; e++) {
    const b = buckets.get(`${i}|${e}`);
    if (!b || b.length < 8) continue;
    const laws = fitLaws(b, i);
    parts.push(`${eraName(e)}: ${laws.length ? laws.join(',') : 'NO-FIT'} (${b.length})`);
  }
  console.log(`cell ${i}:`);
  for (const p of parts) console.log(`   ${p}`);
}
