import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { applyBook, konstE } from '../src/compose.mjs';

// M2 step 4 phase B (P-2026-08-14-f): era self-similarity of the class
// table. B1: era-independent (α, β) for non-reservoir lemmas. B2: β
// affine in R for reservoir-touchers. B3: period-4 fingerprint scaling
// (gen j+4 = 16 × gen j up to boundary corrections + corresponding
// residuals). B4: D_j = S_{j+1} − 2·S_j obeys D_{j+4} = 16·D_j + const.
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
const intervalR = [st.R];
let prev = spellRuns(34n, st);
const sweeps = [];
let lastIv = 0;
for (let nu = 34n; nu < MAXNU - 1n; nu++) {
  advance(nu + 1n);
  const iv = intervalOf(nu + 1n);
  while (intervalR.length <= iv) intervalR.push(st.R);
  const cfg = { runs: prev.map(([b, c]) => [b, konstE(0, c)]), steps: konstE(0, 0n), n0: [] };
  const r = applyBook(cfg, book);
  if (r.result !== 'ok') break;
  sweeps.push({ nu, lemma: r.lemma, steps: simSteps.get(nu + 1n) - simSteps.get(nu) });
  prev = spellRuns(nu + 1n, st);
}
console.log(`${sweeps.length} sweeps replayed`);

// per-(lemma, interval) affine forms
const groups = new Map();
for (const s of sweeps) {
  const key = `${s.lemma}|${intervalOf(s.nu)}`;
  if (!groups.has(key)) groups.set(key, []);
  groups.get(key).push(s);
}
const forms = new Map();   // lemma -> Map(interval -> {alpha, beta, n})
for (const [key, us] of groups) {
  const [lem, iv] = key.split('|').map(Number);
  let alpha = null, beta = null;
  if (us.length >= 2) {
    const dn = us[1].nu - us[0].nu;
    const ds = us[1].steps - us[0].steps;
    if (ds % dn === 0n) {
      alpha = ds / dn;
      beta = us[0].steps - alpha * us[0].nu;
      if (!us.every((u) => alpha * u.nu + beta === u.steps)) { alpha = null; beta = null; }
    }
  }
  if (!forms.has(lem)) forms.set(lem, new Map());
  forms.get(lem).set(iv, { alpha, beta, n: us.length });
}

// ---- B1/B2: era-dependence of (α, β) per lemma ----
let constLemmas = 0, rAffine = 0, varying = 0, multiIv = 0;
const varyingDetail = [];
for (const [lem, byIv] of forms) {
  const ivs = [...byIv.entries()].filter(([, f]) => f.alpha !== null);
  if (ivs.length < 2) continue;
  multiIv++;
  const [, f0] = ivs[0];
  const alphaConst = ivs.every(([, f]) => f.alpha === f0.alpha);
  const betaConst = ivs.every(([, f]) => f.beta === f0.beta);
  if (alphaConst && betaConst) { constLemmas++; continue; }
  if (alphaConst) {
    // β affine in R? slope from first differing pair, then check all
    let slope = null, ok = true;
    for (let a = 0; a < ivs.length && ok; a++) {
      for (let b = a + 1; b < ivs.length && ok; b++) {
        const dR = intervalR[ivs[b][0]] - intervalR[ivs[a][0]];
        const dB = ivs[b][1].beta - ivs[a][1].beta;
        if (dR === 0n) { if (dB !== 0n) ok = false; continue; }
        if (dB % dR !== 0n) { ok = false; continue; }
        const sl = dB / dR;
        if (slope === null) slope = sl;
        else if (sl !== slope) ok = false;
      }
    }
    if (ok && slope !== null) { rAffine++; continue; }
  }
  varying++;
  if (varyingDetail.length < 12) {
    varyingDetail.push(`${lem}: ${ivs.map(([iv, f]) => `iv${iv}(α=${f.alpha},β=${f.beta},R=${intervalR[iv]})`).slice(0, 4).join(' ')}`);
  }
}
console.log(`\nB1/B2 (era dependence, ${multiIv} lemmas firing in ≥2 intervals):`);
console.log(`  (α,β) constant everywhere: ${constLemmas}`);
console.log(`  α constant, β affine in R (one integer slope): ${rAffine}`);
console.log(`  otherwise varying: ${varying}`);
for (const v of varyingDetail) console.log(`    ${v}`);

// ---- B3: period-4 fingerprints ----
const genOf = (nu) => { let j = 0n; while ((1n << (j + 1n)) <= nu) j++; return j; };
const genTable = new Map();   // j -> Map(lemma -> count)
const genTotal = new Map();
for (const s of sweeps) {
  const j = genOf(s.nu);
  if (!genTable.has(j)) { genTable.set(j, new Map()); genTotal.set(j, 0n); }
  const t = genTable.get(j);
  t.set(s.lemma, (t.get(s.lemma) ?? 0n) + 1n);
  genTotal.set(j, genTotal.get(j) + s.steps);
}
console.log('\nB3 (period-4 fingerprint, gen j vs j+4):');
for (let j = 6n; j + 4n <= 17n; j++) {
  const a = genTable.get(j), b = genTable.get(j + 4n);
  let x16 = 0, near = 0, resid = 0;
  const residDetail = [];
  const lems = new Set([...a.keys(), ...b.keys()]);
  for (const lem of lems) {
    const na = a.get(lem) ?? 0n, nb = b.get(lem) ?? 0n;
    if (nb === 16n * na && na > 0n) x16++;
    else if (na > 0n && nb >= 16n * na - 20n && nb <= 16n * na + 20n) near++;
    else { resid++; if (residDetail.length < 10) residDetail.push(`${lem}:${na}→${nb}`); }
  }
  console.log(`  j=${j}→${j + 4n}: ×16 exact ${x16}, ×16±20 ${near}, residual ${resid} [${residDetail.join(' ')}]`);
}

// ---- B4: D_j = S_{j+1} − 2 S_j, test D_{j+4} = 16 D_j + const ----
console.log('\nB4 (second differences):');
const D = new Map();
for (let j = 6n; j <= 16n; j++) D.set(j, genTotal.get(j + 1n) - 2n * genTotal.get(j));
for (let j = 6n; j + 4n <= 16n; j++) {
  const d0 = D.get(j), d4 = D.get(j + 4n);
  console.log(`  j=${j}: D=${d0}   D_{j+4}−16·D_j = ${d4 - 16n * d0}`);
}
