import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { applyBook, konstE } from '../src/compose.mjs';

// Phase B part 2 (P-2026-08-14-g): the N-coefficient theorem.
// Each lemma's slope α = coefficient of its e-run parameter in the PROVEN
// steps expression. 1: book α ≡ fitted α. 2: Σα over generation j equals
// 2^(j+4). 3: Σα doubles exactly (α-weighted boundary cancellation) —
// the mechanism of c' = 2c + 3·2^18. 4: singles skeleton census.
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

// α per lemma from its proven steps expression: coefficient of the e-run
// window parameter (window index L−2, the run below the trailing O^1).
const bookAlpha = book.map((l) => {
  const L = l.blocks.length;
  if (l.blocks[L - 1] !== 10 || l.blocks[L - 2] !== 14) return null;
  const pj = l.params.indexOf(L - 2);
  return pj >= 0 ? l.steps.c[pj] : 0n;
});

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
const sweeps = [];
for (let nu = 34n; nu < MAXNU - 1n; nu++) {
  advance(nu + 1n);
  const cfg = { runs: prev.map(([b, c]) => [b, konstE(0, c)]), steps: konstE(0, 0n), n0: [] };
  const r = applyBook(cfg, book);
  if (r.result !== 'ok') break;
  sweeps.push({ nu, lemma: r.lemma, steps: simSteps.get(nu + 1n) - simSteps.get(nu) });
  prev = spellRuns(nu + 1n, st);
}

// ---- 1: book α ≡ fitted α over multi-member classes ----
const groups = new Map();
for (const s of sweeps) {
  const key = `${s.lemma}|${intervalOf(s.nu)}`;
  if (!groups.has(key)) groups.set(key, []);
  groups.get(key).push(s);
}
let aOk = 0, aBad = 0, aNull = 0;
for (const [key, us] of groups) {
  if (us.length < 2) continue;
  const lem = Number(key.split('|')[0]);
  const dn = us[1].nu - us[0].nu;
  const fitted = (us[1].steps - us[0].steps) / dn;
  const ba = bookAlpha[lem];
  if (ba === null) { aNull++; continue; }
  if (ba === fitted) aOk++;
  else if (aBad++ < 10) console.log(`  α MISMATCH lemma ${lem}: book ${ba} fitted ${fitted}`);
}
console.log(`1. book α ≡ fitted α: ${aOk}/${aOk + aBad} multi-member classes${aNull ? ` (${aNull} without e-tail form)` : ''}`);

// ---- 2 & 3: Σα per generation ----
const genOf = (nu) => { let j = 0n; while ((1n << (j + 1n)) <= nu) j++; return j; };
const sumA = new Map();
let alphaGaps = 0;
for (const s of sweeps) {
  const j = genOf(s.nu);
  const a = bookAlpha[s.lemma];
  if (a === null) { alphaGaps++; continue; }
  sumA.set(j, (sumA.get(j) ?? 0n) + a);
}
if (alphaGaps) console.log(`  (${alphaGaps} sweeps fired lemmas without e-tail form — excluded)`);
console.log('\n2/3. Σα per generation vs 2^(j+4), and doubling:');
for (let j = 7n; j <= 17n; j++) {
  const s = sumA.get(j);
  const target = 1n << (j + 4n);
  const prevS = sumA.get(j - 1n);
  const dbl = prevS !== undefined ? s - 2n * prevS : null;
  console.log(`  j=${j}: Σα=${s}  2^(j+4)=${target} ${s === target ? '≡' : 'MISMATCH Δ=' + (s - target)}  Σα−2Σα₋₁=${dbl ?? '—'}`);
}

// ---- 4: singles skeleton census ----
const singles = [];
for (const [key, us] of groups) {
  if (us.length === 1) singles.push({ lemma: Number(key.split('|')[0]), nu: us[0].nu });
}
const bySkeleton = new Map();
for (const s of singles) {
  const sk = book[s.lemma].blocks.join(',');
  if (!bySkeleton.has(sk)) bySkeleton.set(sk, []);
  bySkeleton.get(sk).push(s.nu);
}
let ladders = 0, laddered = 0, other = 0, singleFam = 0;
for (const [, nus] of bySkeleton) {
  if (nus.length === 1) { singleFam++; continue; }
  nus.sort((a, b) => (a < b ? -1 : 1));
  const ratios = new Set();
  let geometric = true;
  for (let i = 1; i < nus.length; i++) {
    if (nus[i] % nus[i - 1] !== 0n) { geometric = false; break; }
    ratios.add(nus[i] / nus[i - 1]);
  }
  const ok = geometric && [...ratios].every((r) => r === 2n || r === 4n || r === 16n);
  if (ok) { ladders++; laddered += nus.length; }
  else other++;
}
console.log(`\n4. singles: ${singles.length} single-firing classes → ${bySkeleton.size} skeleton families`);
console.log(`   geometric ladders (ratios ⊆ {2,4,16}): ${ladders} families covering ${laddered} firings; ${singleFam} one-off families; ${other} non-ladder`);
console.log(`   ladder coverage of multi-member families: ${(100 * laddered / Math.max(1, singles.length - singleFam)).toFixed(1)}%`);
const fac = (x) => { let k = 0n, o = x; while (o % 2n === 0n) { o /= 2n; k++; } return `${o}·2^${k}`; };
let shown = 0;
for (const [, nus] of bySkeleton) {
  if (nus.length < 4 || shown >= 10) continue;
  shown++;
  nus.sort((a, b) => (a < b ? -1 : 1));
  console.log(`   family[${nus.length}]: ${nus.slice(0, 8).map(fac).join(' ')}${nus.length > 8 ? ' …' : ''}`);
}
