import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { applyBook, konstE } from '../src/compose.mjs';

// M2 step 4 phase A (P-2026-08-14-e): steps as class arithmetic.
// 1. Per-sweep book steps (applied to SPELL configs) ≡ simulator steps.
// 2. steps(ν) affine in ν per (lemma, interval) class — exact, no fit.
// 3. Generation totals from the class formulas ≡ simulator totals.
// 4. Class-level doubling census: which contributions double j→j+1,
//    and what residual the event/deep classes leave (the c'=2c+3·2^18 seed).
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

// ---- ground truth: exact per-anchor step counts from the simulator ----
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const simSteps = new Map();   // nu -> BigInt steps at anchor
runMacro(m, 4, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    const L = s.left;
    if (L.length < 3) return;
    simSteps.set(L[L.length - 2][1] + 2n, s.steps);
  },
});
console.log(`simulator: ${simSteps.size} anchors with exact step counts`);

// ---- 1: per-sweep book steps vs sim, over SPELL configs ----
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
const sweeps = [];   // { nu, lemma, steps }
let okSteps = 0, badSteps = 0;
for (let nu = 34n; nu < MAXNU - 1n; nu++) {
  advance(nu + 1n);
  const cfg = { runs: prev.map(([b, c]) => [b, konstE(0, c)]), steps: konstE(0, 0n), n0: [] };
  const r = applyBook(cfg, book);
  if (r.result !== 'ok') { console.log(`  no lemma at ν=${nu}`); break; }
  const bookStep = r.config.steps.b;
  const truth = simSteps.get(nu + 1n) - simSteps.get(nu);
  if (bookStep === truth) okSteps++;
  else if (badSteps++ < 10) console.log(`  STEP MISMATCH ν=${nu}: book ${bookStep} sim ${truth}`);
  sweeps.push({ nu, lemma: r.lemma, steps: truth });
  prev = spellRuns(nu + 1n, st);
}
console.log(`1. per-sweep steps: ${okSteps}/${sweeps.length} book ≡ sim${badSteps ? ` (${badSteps} MISMATCHES)` : ''}`);

// ---- 2: steps affine in ν per (lemma, interval) ----
const groups = new Map();   // `${lemma}|${interval}` -> [{nu, steps}]
for (const s of sweeps) {
  const key = `${s.lemma}|${intervalOf(s.nu)}`;
  if (!groups.has(key)) groups.set(key, []);
  groups.get(key).push(s);
}
let affOk = 0, affBad = 0, affSingle = 0;
const classForms = new Map();   // key -> {alpha, beta}
for (const [key, us] of groups) {
  if (us.length === 1) { affSingle++; classForms.set(key, { alpha: 0n, beta: us[0].steps, members: us }); continue; }
  const [a, b] = us;
  const dn = b.nu - a.nu;
  const ds = b.steps - a.steps;
  if (ds % dn !== 0n) { affBad++; continue; }
  const alpha = ds / dn;
  const beta = a.steps - alpha * a.nu;
  const exact = us.every((u) => alpha * u.nu + beta === u.steps);
  if (exact) { affOk++; classForms.set(key, { alpha, beta, members: us }); }
  else if (affBad++ < 10) console.log(`  NON-AFFINE class ${key} (${us.length} members)`);
}
console.log(`2. affine classes: ${affOk}/${affOk + affBad} multi-member exact${affBad ? ` (${affBad} FAIL)` : ''}; ${affSingle} singletons`);

// ---- 3: generation totals from class formulas vs simulator ----
console.log('\n3. generation totals (class arithmetic vs simulator):');
const genTotals = [];
for (let j = 6n; j <= 17n; j++) {
  const lo = 1n << j, hi = 1n << (j + 1n);
  let simTotal = 0n;
  const byClass = new Map();
  for (const s of sweeps) {
    if (s.nu < lo || s.nu >= hi) continue;
    simTotal += s.steps;
    const key = `${s.lemma}|${intervalOf(s.nu)}`;
    if (!byClass.has(key)) byClass.set(key, { n: 0n, sumNu: 0n });
    const g = byClass.get(key);
    g.n++; g.sumNu += s.nu;
  }
  let classTotal = 0n;
  let formulaMiss = false;
  for (const [key, g] of byClass) {
    const f = classForms.get(key);
    if (!f) { formulaMiss = true; break; }
    classTotal += f.alpha * g.sumNu + f.beta * g.n;
  }
  const ok = !formulaMiss && classTotal === simTotal;
  genTotals.push({ j, simTotal, nClasses: byClass.size, byClass });
  console.log(`  j=${j}: sim ${simTotal}  classes ${byClass.size}  formulas ${ok ? '≡ EXACT' : 'MISMATCH'}`);
}

// ---- 4: doubling census j → j+1 ----
console.log('\n4. doubling census (member counts, generation j vs j+1):');
for (let i = 0; i + 1 < genTotals.length; i++) {
  const a = genTotals[i], b = genTotals[i + 1];
  let doubled = 0, other = 0;
  const lemCount = (gt) => {
    const mm = new Map();
    for (const [key, g] of gt.byClass) {
      const lem = key.split('|')[0];
      mm.set(lem, (mm.get(lem) ?? 0n) + g.n);
    }
    return mm;
  };
  const la = lemCount(a), lb = lemCount(b);
  const residualLemmas = [];
  for (const [lem, nb] of lb) {
    const na = la.get(lem) ?? 0n;
    if (nb === 2n * na) doubled++;
    else { other++; residualLemmas.push(`${lem}:${na}→${nb}`); }
  }
  console.log(`  j=${a.j}→${b.j}: ${doubled} lemmas double exactly, ${other} residual${other ? ` [${residualLemmas.slice(0, 8).join(' ')}]` : ''}`);
}
