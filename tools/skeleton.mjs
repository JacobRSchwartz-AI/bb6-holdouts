import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { applyBook, konstE } from '../src/compose.mjs';

// Phase B part 3 (P-2026-08-14-h): skeleton k-parametrization of the
// singles. Each single-firing (lemma, interval) row = (ν, t, steps) with
// t = trailing-ones(ν). Per skeleton family: exact affine fit
// steps = α·ν + γ·t + δ (BigInt Cramer, det-scaled verification), and
// the position ladder ν+1 = q·2^a (few q's, one firing per slot).
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const O = 10, E = 14, A = 11, F = 15;
const GLYPH = [O, E, A, F];
const MAXNU = 266384n;

function calendarEvents(maxNu) {
  const ev = [];
  for (let k = 5n; (1n << k) <= maxNu; k++) {
    const p = 1n << k;
    const r = k % 4n;
    if (r === 0n) ev.push([p, 'respell']);
    if (r === 1n) { ev.push([p, 'pay']); ev.push([3n * p, 'pay']); }
    if (r === 2n) { ev.push([p, 'respell']); ev.push([3n * p, 'pay']); ev.push([5n * p, 'borrow']); }
    if (r === 3n) ev.push([3n * p, 'pay']);
  }
  return ev.filter(([p]) => p > 34n && p <= maxNu).sort((x, y) => (x[0] < y[0] ? -1 : 1));
}
const PREAMBLE = [
  [34n, [[A, 1n], [O, 4n], [E, 1n], [A, 1n], [O, 1n]]],
  [64n, [[A, 1n], [O, 4n], [E, 1n], [A, 1n], [E, 1n]]],
  [256n, [[A, 1n], [O, 4n], [A, 1n], [O, 2n]]],
  [1024n, [[A, 1n], [O, 4n], [A, 1n], [O, 1n], [E, 1n]]],
  [4096n, [[A, 1n], [O, 4n], [F, 1n], [A, 1n], [O, 1n]]],
  [16384n, [[A, 1n], [O, 4n], [F, 1n], [A, 1n], [E, 1n]]],
  [65536n, [[A, 1n], [O, 3n], [F, 1n], [O, 3n]]],
  [262144n, [[A, 1n], [O, 3n], [F, 1n], [O, 2n], [E, 1n]]],
];
const preambleAt = (nu) => {
  let p = PREAMBLE[0][1];
  for (const [from, runs] of PREAMBLE) if (nu >= from) p = runs;
  return p;
};
function cellGlyph(i, nu) {
  if (i === 0) return O;
  const r = (i - 1) % 3;
  if (r === 0) {
    const s = i === 1 ? 0n : BigInt(4 * ((i - 4) / 3) + 4);
    return ((nu >> s) & 1n) === 1n ? F : O;
  }
  const mt = r === 1 ? (i - 2) / 3 : (i - 3) / 3;
  return GLYPH[Number((nu >> BigInt(4 * mt + r)) & 3n)];
}
function spellRuns(nu, st) {
  const runs = [];
  for (const [b, c] of preambleAt(nu)) runs.push([b, c]);
  runs.push([st.font, st.R]);
  for (let i = st.len - 1; i >= 0; i--) runs.push([cellGlyph(i, nu), 1n]);
  runs.push([F, 1n]); runs.push([E, nu - 2n]); runs.push([O, 1n]);
  const out = [];
  for (const [b, c] of runs) {
    if (out.length && out[out.length - 1][0] === b) out[out.length - 1][1] += c;
    else out.push([b, c]);
  }
  return out;
}

const raw = JSON.parse(readFileSync('data/book.json', 'utf8'));
const deE = (e) => ({ c: e.c.map(BigInt), b: BigInt(e.b) });
const book = raw.map((l) => ({
  ...l,
  counts: l.counts.map(BigInt),
  post: l.post.map(([b, e]) => [b, deE(e)]),
  steps: deE(l.steps),
  n0: l.n0.map(BigInt),
}));

const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const simSteps = new Map();
runMacro(m, 4, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    const L = s.left;
    if (L.length < 3) return;
    simSteps.set(L[L.length - 2][1] + 2n, s.steps);
  },
});

const events = calendarEvents(MAXNU);
const boundaries = [34n, ...events.map(([p]) => p), MAXNU];
const intervalOf = (nu) => {
  let k = 0;
  while (k + 1 < boundaries.length && nu >= boundaries[k + 1]) k++;
  return k;
};
const st = { font: E, R: 202n, len: 5 };
let evIdx = 0;
const advance = (nu) => {
  while (evIdx < events.length && events[evIdx][0] <= nu) {
    const [, type] = events[evIdx++];
    if (type === 'pay') { st.len++; st.R -= 1n; }
    else if (type === 'borrow') { st.len--; st.R += 1n; }
    else st.font = st.font === E ? A : E;
  }
};
advance(34n);
let prev = spellRuns(34n, st);
const groups = new Map();
for (let nu = 34n; nu < MAXNU - 1n; nu++) {
  advance(nu + 1n);
  const cfg = { runs: prev.map(([b, c]) => [b, konstE(0, c)]), steps: konstE(0, 0n), n0: [] };
  const r = applyBook(cfg, book);
  if (r.result !== 'ok') break;
  const key = `${r.lemma}|${intervalOf(nu)}`;
  if (!groups.has(key)) groups.set(key, []);
  groups.get(key).push({ nu, steps: simSteps.get(nu + 1n) - simSteps.get(nu), lemma: r.lemma });
  prev = spellRuns(nu + 1n, st);
}

// R and len per interval (for the era-affine regressors)
const ivState = [];
{
  let R = 202n, len = 5n;
  ivState.push({ R, len });
  for (const [, type] of events) {
    if (type === 'pay') { len += 1n; R -= 1n; }
    else if (type === 'borrow') { len -= 1n; R += 1n; }
    ivState.push({ R, len });
  }
}

const trailingOnes = (x) => { let t = 0n; while ((x & 1n) === 1n) { x >>= 1n; t++; } return t; };
const singles = [];
for (const [, us] of groups) if (us.length === 1) singles.push(us[0]);
const bySkeleton = new Map();
for (const s of singles) {
  const sk = book[s.lemma].blocks.join(',');
  if (!bySkeleton.has(sk)) bySkeleton.set(sk, []);
  const iv = ivState[intervalOf(s.nu)];
  bySkeleton.get(sk).push({ nu: s.nu, t: trailingOnes(s.nu), R: iv.R, len: iv.len, steps: s.steps });
}

// Exact linear-model test over BigInt rationals: z ∈ span(columns of X)
// iff rank(X) == rank(X|z). Gaussian elimination with exact fractions.
const gcdB = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const frac = (n, d = 1n) => { if (d < 0n) { n = -n; d = -d; } const g = gcdB(n, d) || 1n; return [n / g, d / g]; };
const fSub = (a, b) => frac(a[0] * b[1] - b[0] * a[1], a[1] * b[1]);
const fMul = (a, b) => frac(a[0] * b[0], a[1] * b[1]);
const fDiv = (a, b) => frac(a[0] * b[1], a[1] * b[0]);
function bareissRank(rowsIn) {
  const M = rowsIn.map((r) => r.map((v) => frac(v)));
  const nr = M.length, nc = M[0].length;
  let rank = 0;
  for (let col = 0; col < nc && rank < nr; col++) {
    let piv = -1;
    for (let r = rank; r < nr; r++) if (M[r][col][0] !== 0n) { piv = r; break; }
    if (piv < 0) continue;
    [M[rank], M[piv]] = [M[piv], M[rank]];
    for (let r = rank + 1; r < nr; r++) {
      if (M[r][col][0] === 0n) continue;
      const f = fDiv(M[r][col], M[rank][col]);
      for (let c = col; c < nc; c++) M[r][c] = fSub(M[r][c], fMul(f, M[rank][c]));
    }
    rank++;
  }
  return rank;
}
const qa = (nu) => { let w = nu + 1n, a = 0n; while (w % 2n === 0n) { w /= 2n; a++; } return [w, a]; };
// respell indicators: ν+1 = 2^k with k even (k≡2: e→a, k≡0: a→e)
const resp = (r) => {
  const [q, a] = qa(r.nu);
  if (q !== 1n) return [0n, 0n];
  return [a % 4n === 2n ? 1n : 0n, a % 4n === 0n ? 1n : 0n];
};
const REGS = [
  ['ν,t,⌊t/4⌋', (r) => [r.nu, r.t, r.t / 4n, 1n]],
  ['+respell', (r) => {
    const [r2, r0] = resp(r);
    return [r.nu, r.t, r.t / 4n, r2, r2 * r.t, r2 * (r.t / 4n), r0, r0 * r.t, r0 * (r.t / 4n), 1n];
  }],
  ['+R,len', (r) => {
    const [r2, r0] = resp(r);
    return [r.nu, r.t, r.t / 4n, r.R, r.len, r2, r2 * r.t, r2 * (r.t / 4n), r0, r0 * r.t, r0 * (r.t / 4n), 1n];
  }],
];
function fitAffine(rows) {
  for (const [name, reg] of REGS) {
    const X = rows.map(reg);
    const nCols = X[0].length;
    const margin = rows.length - nCols;
    if (margin < 1) continue;
    const Xz = rows.map((r, i) => [...X[i], r.steps]);
    if (bareissRank(X) === bareissRank(Xz)) return { kind: name, margin };
  }
  return null;
}

console.log(`${singles.length} singles → ${bySkeleton.size} skeleton families\n`);
let pass = 0, passSplit = 0, fail = 0, small = 0;
let ladderOk = 0, ladderFail = 0;
const failDetail = [];
for (const [sk, rows] of bySkeleton) {
  rows.sort((a, b) => (a.nu < b.nu ? -1 : 1));
  // position ladder: ν+1 = q·2^a
  const slots = new Map();
  let dup = false;
  const qs = new Set();
  for (const r of rows) {
    let w = r.nu + 1n, a = 0n;
    while (w % 2n === 0n) { w /= 2n; a++; }
    qs.add(w);
    const slot = `${w}|${a}`;
    if (slots.has(slot)) dup = true;
    slots.set(slot, true);
  }
  const ladder = !dup && qs.size <= 4;
  if (rows.length >= 4) { if (ladder) ladderOk++; else ladderFail++; }
  // affine model
  if (rows.length < 4) { small++; continue; }
  const f = fitAffine(rows);
  if (f) { pass++; console.log(`  pass[${rows.length}] tier=${f.kind} margin=${f.margin}`); continue; }
  // split by ν mod 8
  const parts = new Map();
  for (const r of rows) {
    const p = (r.nu % 8n).toString();
    if (!parts.has(p)) parts.set(p, []);
    parts.get(p).push(r);
  }
  const bigParts = [...parts.values()].filter((p) => p.length >= 4);
  if (bigParts.length && bigParts.every((p) => fitAffine(p))) { passSplit++; continue; }
  fail++;
  if (failDetail.length < 6) {
    failDetail.push(`  [${rows.length}] q-set={${[...qs].slice(0, 6).join(',')}} rows: ${rows.slice(0, 5).map((r) => `(ν=${r.nu},t=${r.t},s=${r.steps})`).join(' ')}`);
  }
}
console.log(`affine model steps = α·ν + γ·t + δ (families with ≥4 members):`);
console.log(`  pass whole-family: ${pass}   pass after mod-8 split: ${passSplit}   FAIL: ${fail}   (small families <4: ${small})`);
console.log(`position ladder ν+1 = q·2^a, ≤4 q's, one firing per slot: ${ladderOk} ok, ${ladderFail} not`);
if (failDetail.length) { console.log('\nfailed families:'); for (const d of failDetail) console.log(d); }

// full dump of failing families: offset = steps − 16ν vs (t, q, a)
console.log('\ndiagnostic (offset = steps − 16ν):');
for (const [sk, rows] of bySkeleton) {
  if (rows.length < 4 || fitAffine(rows)) continue;
  console.log(`family[${rows.length}]:`);
  for (const r of rows.slice(0, 70)) {
    const [q, a] = qa(r.nu);
    console.log(`  ν=${String(r.nu).padStart(7)} t=${String(r.t).padStart(2)} q=${String(q).padStart(4)} a=${String(a).padStart(2)} R=${r.R} len=${r.len} off=${r.steps - 16n * r.nu}`);
  }
}
