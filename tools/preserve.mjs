import { readFileSync } from 'node:fs';
import { applyLemma, applyBook, konstE } from '../src/compose.mjs';

// M2 step 3 — per-lemma preservation (P-2026-08-14-c): SPELL(ν) ⊢_book
// SPELL(ν+1). Phase 1: replay every transition TM-free (host = SPELL(ν),
// advance by first-match lemma, compare to SPELL(ν+1)). Phase 2: per fired
// lemma, window reach in ν-bits, residue purity at that reach, class
// density per calendar interval. Phase 3: one symbolic application per
// (lemma, interval) with the tail e-run count formal (ν = r + 2^d·T),
// exact run-list equality demanded. purity ∧ density ∧ (reach ≤ depth) ∧
// symbolic identity together carry the ∀ over each class.
const O = 10, E = 14, A = 11, F = 15;
const GLYPH = [O, E, A, F];
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };
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
const cellBits = (i) => {
  if (i === 0) return [];
  const r = (i - 1) % 3;
  if (r === 0) return [i === 1 ? 0 : 4 * ((i - 4) / 3) + 4];
  const mt = r === 1 ? (i - 2) / 3 : (i - 3) / 3;
  return [4 * mt + r, 4 * mt + r + 1];
};

// spell with the e-run count as a caller-supplied expr; all other counts
// concrete E-exprs of dimension gDim.
function spellRuns(nu, st, gDim, eExpr) {
  const runs = [];
  for (const [b, c] of preambleAt(nu)) runs.push([b, konstE(gDim, c)]);
  runs.push([st.font, konstE(gDim, st.R)]);
  for (let i = st.len - 1; i >= 0; i--) runs.push([cellGlyph(i, nu), konstE(gDim, 1n)]);
  runs.push([F, konstE(gDim, 1n)]);
  runs.push([E, eExpr ?? konstE(gDim, nu - 2n)]);
  runs.push([O, konstE(gDim, 1n)]);
  const out = [];
  for (const [b, e] of runs) {
    const top = out[out.length - 1];
    if (top && top[0] === b) top[1] = { c: top[1].c.map((v, i) => v + e.c[i]), b: top[1].b + e.b };
    else out.push([b, e]);
  }
  return out;
}
const eqE = (e, f) => e.b === f.b && e.c.length === f.c.length && e.c.every((v, i) => v === f.c[i]);
const runsEq = (x, y) => x.length === y.length && x.every(([b, e], i) => b === y[i][0] && eqE(e, y[i][1]));
const fmtRuns = (rs) => rs.map(([b, e]) => `${NAME[b] ?? b}^${e.c.length ? `${e.c[0]}T+${e.b}` : e.b}`).join(' ');

const raw = JSON.parse(readFileSync('data/book.json', 'utf8'));
const deE = (e) => ({ c: e.c.map(BigInt), b: BigInt(e.b) });
const book = raw.map((l) => ({
  ...l,
  counts: l.counts.map(BigInt),
  post: l.post.map(([b, e]) => [b, deE(e)]),
  steps: deE(l.steps),
  n0: l.n0.map(BigInt),
}));

const events = calendarEvents(MAXNU);
const boundaries = [34n, ...events.map(([p]) => p), MAXNU];
const intervalOf = (nu) => {
  let k = 0;
  while (k + 1 < boundaries.length && nu >= boundaries[k + 1]) k++;
  return k;
};

// ---- phase 1: TM-free concrete replay over SPELL configs ----
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
let prev = spellRuns(34n, st, 0);
let prevState = { ...st };
const fired = new Map();   // lemmaIdx -> [nu...]
let p1ok = 0;
const p1fails = [];
for (let nu = 34n; nu < MAXNU - 1n; nu++) {
  advance(nu + 1n);
  const cur = spellRuns(nu + 1n, st, 0);
  const cfg = { runs: prev.map(([b, e]) => [b, e]), steps: konstE(0, 0n), n0: [] };
  const r = applyBook(cfg, book);
  if (r.result !== 'ok' || !runsEq(r.config.runs, cur)) {
    if (p1fails.length < 10) p1fails.push({ nu, why: r.result, got: r.config && fmtRuns(r.config.runs), want: fmtRuns(cur) });
  } else {
    p1ok++;
    if (!fired.has(r.lemma)) fired.set(r.lemma, []);
    fired.get(r.lemma).push({ nu, state: prevState });
  }
  prev = cur;
  prevState = { ...st };
}
console.log(`phase 1 (TM-free replay): ${p1ok}/${Number(MAXNU - 35n)} transitions exact, ${fired.size} distinct lemmas fired`);
for (const f of p1fails) console.log(`  FAIL ν=${f.nu} ${f.why}\n    got : ${f.got}\n    want: ${f.want}`);

// ---- phase 2: per-lemma window reach, residue purity, density ----
// map runs -> cell span; returns per-run [cellLo, cellHi) for zone runs,
// null for preamble/reservoir/tail runs.
function cellSpans(runs, state) {
  const spans = new Array(runs.length).fill(null);
  let cell = 0;
  for (let i = runs.length - 4; i >= 0; i--) {
    const cnt = Number(runs[i][1].b);
    // stop at the reservoir: identified as the run whose count exceeds the
    // number of cells that could remain
    if (cell + cnt > state.len) { spans[i] = [cell, state.len, true]; break; }
    spans[i] = [cell, cell + cnt, false];
    cell += cnt;
    if (cell === state.len) break;
  }
  return spans;
}

const lemmaMeta = new Map();
const v2 = (x) => { let k = 0n; while (x % 2n === 0n && x > 0n) { x /= 2n; k++; } return k; };
for (const [li, uses] of fired) {
  const lemma = book[li];
  const nus = uses.map((u) => u.nu);
  // residue purity at measured depth
  let g = 0n;
  for (let i = 1; i < nus.length; i++) { let d = nus[i] - nus[0]; if (d < 0n) d = -d; g = g === 0n ? d : gcd(g, d); }
  const dPure = nus.length > 1 ? v2(g) : null;
  // window reach at a representative firing
  const rep = uses[Math.floor(uses.length / 2)];
  const runs = spellRuns(rep.nu, rep.state, 0);
  const L = lemma.blocks.length;
  const base = runs.length - L;
  const spans = cellSpans(runs, rep.state);
  const preLen = preambleAt(rep.nu).length;
  let maxBit = -1, resTouch = false, pinsE = false;
  for (let i = base; i < runs.length; i++) {
    if (i <= preLen) { resTouch = true; continue; }
    if (i >= runs.length - 3) {
      // tail: the e-run must be formal for a multi-ν class
      if (i === runs.length - 2 && !lemma.params.includes(i - base)) pinsE = true;
      continue;
    }
    const span = spans[i];
    if (!span) { resTouch = true; continue; }
    let [lo, hi, isRes] = span;
    if (isRes) resTouch = true;
    if (i === base && lemma.withContext && !lemma.params.includes(0)) {
      // only the bottom (rightmost) lemma.counts[0] cells are in-window
      const c0 = Number(lemma.counts[0]);
      if (hi - lo > c0) hi = lo + c0;
    }
    for (let cIdx = lo; cIdx < hi; cIdx++) for (const bit of cellBits(cIdx)) if (bit > maxBit) maxBit = bit;
  }
  const dEff = maxBit + 1;
  // purity at dEff and density per interval
  const mod = 1n << BigInt(dEff);
  const r0 = ((nus[0] % mod) + mod) % mod;
  const pureAtReach = nus.every((n) => n % mod === r0);
  let dense = true;
  const byIv = new Map();
  for (const u of uses) {
    const k = intervalOf(u.nu);
    if (!byIv.has(k)) byIv.set(k, []);
    byIv.get(k).push(u);
  }
  const denseMisses = [];
  if (pureAtReach && dEff >= 0) {
    for (const [k, us] of byIv) {
      const lo = us[0].nu, hi = us[us.length - 1].nu;
      let expect = 0n;
      for (let n = lo; n <= hi; n += 1n) if (n % mod === r0) expect++;
      if (BigInt(us.length) !== expect) { dense = false; denseMisses.push({ k, have: us.length, expect, lo, hi }); }
    }
  }
  if (denseMisses.length) console.log(`  density break: lemma ${li} r=${r0} mod=${mod}: ${denseMisses.map((d) => `iv${d.k} ${d.have}/${d.expect} [${d.lo},${d.hi}]`).join('; ')}`);
  lemmaMeta.set(li, { uses, byIv, dPure, dEff, r0, mod, pureAtReach, dense, resTouch, pinsE, single: nus.length === 1 });
}
function gcd(a, b) { while (b) { [a, b] = [b, a % b]; } return a; }

let nPure = 0, nDense = 0, nReachOk = 0, nResTouch = 0, nPins = 0, nSingle = 0;
const reachViolations = [];
for (const [li, m] of lemmaMeta) {
  if (m.single) { nSingle++; continue; }
  if (m.pinsE) { nPins++; continue; }
  if (m.pureAtReach) nPure++; else reachViolations.push(li);
  if (m.dense) nDense++;
  if (m.dPure !== null && BigInt(m.dEff) <= m.dPure) nReachOk++;
  if (m.resTouch) nResTouch++;
}
const nMulti = [...lemmaMeta.values()].filter((m) => !m.single && !m.pinsE).length;
console.log(`\nphase 2 (classes): ${nMulti} multi-use ∀-lemmas | pure-at-reach ${nPure}/${nMulti} | dense ${nDense}/${nMulti} | reach≤depth ${nReachOk}/${nMulti} | reservoir-touching ${nResTouch} | e-pinned ${nPins} | single-use ${nSingle}`);
if (reachViolations.length) console.log(`  purity violations at own reach: lemmas ${reachViolations.slice(0, 10).join(', ')}`);

// ---- phase 3: symbolic identity per (lemma, interval) ----
let p3pass = 0, p3total = 0, p3skip1 = 0;
const p3fails = [];
for (const [li, m] of lemmaMeta) {
  if (m.pinsE) continue;
  for (const [k, us] of m.byIv) {
    if (us.length < 2) { p3skip1++; continue; }
    p3total++;
    const rep = us[Math.floor(us.length / 2)];
    const d = m.pureAtReach ? BigInt(m.dEff) : (m.dPure ?? 0n);
    const mod = 1n << d;
    const r = rep.nu % mod;
    const T0 = (us[0].nu - r) / mod;
    const Trep = (rep.nu - r) / mod;
    // host: SPELL(rep.nu) with e-count = mod·T + (r − 2); target likewise +1
    const eHost = { c: [mod], b: r - 2n };
    const eTgt = { c: [mod], b: r - 1n };
    const host = spellRuns(rep.nu, rep.state, 1, eHost);
    // state for ν+1 equals rep.state (no event inside an interval)
    const tgt = spellRuns(rep.nu + 1n, rep.state, 1, eTgt);
    const cfg = { runs: host, steps: konstE(1, 0n), n0: [T0] };
    const res = applyLemma(cfg, book[li]);
    if (res.result === 'ok' && runsEq(res.config.runs, tgt)) p3pass++;
    else if (p3fails.length < 10) p3fails.push({ li, k, nu: rep.nu, why: res.result, got: res.config && fmtRuns(res.config.runs), want: fmtRuns(tgt) });
  }
}
console.log(`\nphase 3 (symbolic, e-run formal): ${p3pass}/${p3total} (lemma, interval) pairs exact; ${p3skip1} single-firing pairs left concrete`);
for (const f of p3fails) console.log(`  FAIL lemma ${f.li} iv ${f.k} ν=${f.nu} ${f.why}\n    got : ${f.got}\n    want: ${f.want}`);

// ---- phase 2b/3b: binding-group refinement for the parametric lemmas ----
// A lemma whose window binds a deep run's count formally fires on a FAMILY
// of residue classes, one per binding value; purity/symbolic-identity are
// per-group statements, with the cross-group ∀ carried by the lemma's own
// formal tape proof (and the arithmetic layer, step 4).
const bindingsAt = (lemma, u) => {
  const runs = spellRuns(u.nu, u.state, 0);
  const base = runs.length - lemma.blocks.length;
  const L = lemma.blocks.length;
  const out = {};
  for (let j = 0; j < lemma.params.length; j++) {
    const i = lemma.params[j];
    if (i === L - 2 && base + i === runs.length - 2) continue;   // the e-run param
    out[i] = runs[base + i][1].b;
  }
  return JSON.stringify(out, (k, v) => (typeof v === 'bigint' ? v.toString() : v));
};

let gTotal = 0, gPure = 0, g3total = 0, g3pass = 0, g3single = 0;
const gFails = [];
for (const [li, m] of lemmaMeta) {
  if (m.single || m.pinsE || m.pureAtReach) continue;
  const lemma = book[li];
  const groups = new Map();
  for (const u of m.uses) {
    const key = bindingsAt(lemma, u);
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(u);
  }
  for (const [key, us] of groups) {
    gTotal++;
    // group reach + purity
    const rep = us[Math.floor(us.length / 2)];
    const runs = spellRuns(rep.nu, rep.state, 0);
    const base = runs.length - lemma.blocks.length;
    const spans = cellSpans(runs, rep.state);
    const preLen = preambleAt(rep.nu).length;
    let maxBit = -1;
    for (let i = base; i < runs.length - 3; i++) {
      if (i <= preLen) continue;
      const span = spans[i];
      if (!span) continue;
      let [lo, hi] = span;
      if (i === base && lemma.withContext && !lemma.params.includes(0)) {
        const c0 = Number(lemma.counts[0]);
        if (hi - lo > c0) hi = lo + c0;
      }
      for (let c = lo; c < hi; c++) for (const bit of cellBits(c)) if (bit > maxBit) maxBit = bit;
    }
    const mod = 1n << BigInt(maxBit + 1);
    const r0 = us[0].nu % mod;
    const pure = us.every((u) => u.nu % mod === r0);
    if (pure) gPure++;
    // symbolic per (group, interval)
    const byIv = new Map();
    for (const u of us) {
      const k = intervalOf(u.nu);
      if (!byIv.has(k)) byIv.set(k, []);
      byIv.get(k).push(u);
    }
    for (const [k, ius] of byIv) {
      if (ius.length < 2) { g3single++; continue; }
      g3total++;
      const irep = ius[Math.floor(ius.length / 2)];
      const T0 = (ius[0].nu - irep.nu % mod) / mod;
      const eHost = { c: [mod], b: (irep.nu % mod) - 2n };
      const eTgt = { c: [mod], b: (irep.nu % mod) - 1n };
      const host = spellRuns(irep.nu, irep.state, 1, eHost);
      const tgt = spellRuns(irep.nu + 1n, irep.state, 1, eTgt);
      const res = applyLemma({ runs: host, steps: konstE(1, 0n), n0: [T0] }, lemma);
      if (res.result === 'ok' && runsEq(res.config.runs, tgt)) g3pass++;
      else if (gFails.length < 10) gFails.push({ li, k, nu: irep.nu, why: res.result, got: res.config && fmtRuns(res.config.runs), want: fmtRuns(tgt) });
    }
  }
}
console.log(`\nphase 2b/3b (parametric lemmas, grouped by deep-run binding): ${gTotal} groups | pure ${gPure}/${gTotal} | symbolic ${g3pass}/${g3total} (interval,group) pairs exact | ${g3single} single-firing pairs concrete`);
for (const f of gFails) console.log(`  FAIL lemma ${f.li} iv ${f.k} ν=${f.nu} ${f.why}\n    got : ${f.got}\n    want: ${f.want}`);
