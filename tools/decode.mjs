import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// M2d step 3: learn the zone's number system. At anchor ν = N+2, the
// numeral zone (runs between the M-reservoir's 1010^K budget run and the
// fixed `1111^1 1110^N 1010^1` tail) should spell a value tied to ν in
// some digit system. Print zone vs ν side by side for structured ranges,
// then fit digit weights.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

const anchors = [];
runMacro(m, K_BLOCK, {
  maxOps: 2e6, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    anchors.push(s.left.map(([b, c]) => [b, c]));
  },
});
console.log(`${anchors.length} anchors`);

const fmt = (L) => L.map(([b, c]) => `${b.toString(2).padStart(4, '0')}${c > 1n ? '^' + c : ''}`).join(' ');

// Decoder fit: zone runs (strictly between the M-run and the tail's 1111)
// read as digit string; try digit-value assignments and alignments so that
// value(zone) is an affine function of ν, consistently across all anchors.
// The M-run is the big run (count > 60) left of the zone.
function zoneOf(L) {
  // tail = 1111^1 1110^N 1010^1; find the last big 1110 run (the N-run)
  if (L.length < 5) return null;
  const nIdx = L.length - 2;
  if (L[nIdx][0] !== 0b1110) return null;
  const sepIdx = nIdx - 1;                    // the 1111 separator
  if (L[sepIdx][0] !== 0b1111 || L[sepIdx][1] !== 1n) return null;
  // scan left for the M-run: first run with count >= 60
  let mIdx = -1;
  for (let i = sepIdx - 1; i >= 0; i--) {
    if (L[i][1] >= 60n) { mIdx = i; break; }
  }
  if (mIdx < 0) return null;
  return L.slice(mIdx + 1, sepIdx);
}

// Sliding-window decoder test: hypothesis — with v = ν − 2^(L+1) (L = zone
// digit count) and symbols O,e,a,f = 0,1,2,3, zone digit p_i (i-th from the
// right, i ≥ 2) equals floor(v / 2^(i−1)) mod 4: overlapping 2-bit windows
// of v, i.e. the "shift-overflow" redundancy. p1/p0 are head-phase cells.
{
  const VAL = { 0b1010: 0n, 0b1110: 1n, 0b1011: 2n, 0b1111: 3n };
  let anchorsTested = 0, anchorsExact = 0;
  const digitFails = new Map();
  const failNus = [];
  for (const L of anchors) {
    if (L.length < 6) continue;
    const nu = L[L.length - 2][1] + 2n;
    if (nu < 34n) continue;
    const z = zoneOf(L);
    if (!z || z.length === 0) continue;
    const digits = [];
    for (const [b, c] of z) for (let r = 0n; r < c; r++) digits.push(VAL[b]);
    const len = BigInt(digits.length);
    const v = nu - (1n << (len + 1n));
    if (v < 0n) continue;
    anchorsTested++;
    let ok = true;
    for (let i = 2; i < digits.length; i++) {
      const got = digits[digits.length - 1 - i];
      let want;
      if (i <= 3) want = (v >> BigInt(i - 1)) & 3n;          // sliding 2-bit window
      else want = ((v >> BigInt(i)) & 1n) * (i % 2 === 0 ? 3n : 1n);   // plain bit; set = f/e by position parity
      if (got !== want) {
        ok = false;
        digitFails.set(i, (digitFails.get(i) ?? 0) + 1);
        if (failNus.length < 14) failNus.push(`ν=${nu} p${i}: got ${got} want ${want} (v=${v}, v mod 2^${i + 1}=${v % (1n << BigInt(i + 1))})`);
      }
    }
    if (ok) anchorsExact++;
  }
  console.log(`hybrid model: ${anchorsExact}/${anchorsTested} anchors exact on all digits i>=2`);
  console.log('digit-position fail counts:', JSON.stringify([...digitFails.entries()].sort((a, b) => a[0] - b[0])));
  console.log('fails:', failNus.join('\n  '));
  // print maximal intervals of failing ν with factored endpoints
  const factored = (x) => { let k = 0n, o = x; while (o % 2n === 0n && o > 0n) { o /= 2n; k++; } return `${o}·2^${k}`; };
  const failList = [];
  for (const L of anchors) {
    if (L.length < 6) continue;
    const nu = L[L.length - 2][1] + 2n;
    if (nu < 34n) continue;
    const z = zoneOf(L);
    if (!z || z.length === 0) continue;
    const digits = [];
    for (const [b, c] of z) for (let r = 0n; r < c; r++) digits.push(VAL[b]);
    const len = BigInt(digits.length);
    const v = nu - (1n << (len + 1n));
    if (v < 0n) continue;
    let ok = true;
    for (let i = 2; i < digits.length; i++) {
      const got = digits[digits.length - 1 - i];
      let want;
      if (i <= 3) want = (v >> BigInt(i - 1)) & 3n;
      else want = ((v >> BigInt(i)) & 1n) * (i % 2 === 0 ? 3n : 1n);
      if (got !== want) { ok = false; break; }
    }
    if (!ok) failList.push(nu);
  }
  failList.sort((a, b) => (a < b ? -1 : 1));
  const intervals = [];
  for (const nu of failList) {
    const last = intervals[intervals.length - 1];
    if (last && nu === last[1] + 1n) last[1] = nu;
    else intervals.push([nu, nu]);
  }
  console.log(`${failList.length} failing anchors in ${intervals.length} maximal intervals:`);
  for (const [a, b] of intervals.slice(0, 25)) console.log(`  [${a}, ${b}] = [${factored(a)}, ${factored(b + 1n)})  span ${b - a + 1n}`);
}

// Pair-context decoder: α(spelling) = Σ_i w(s_i, left-neighbor) · 2^i
// (i = 0 at the rightmost zone digit; leftmost digit's neighbor is the
// boundary symbol 'B'). Solve the exact linear system w over rationals
// from observed (spelling, ν) pairs; then verify on ALL anchors.
const SYM = { 0b1010: 'O', 0b1011: 'a', 0b1110: 'e', 0b1111: 'f' };
const pairs = [];
const pairIdx = new Map();
const idxOf = (p) => {
  if (!pairIdx.has(p)) { pairIdx.set(p, pairs.length); pairs.push(p); }
  return pairIdx.get(p);
};
const rows = [];
for (const L of anchors) {
  if (L.length < 6) continue;
  const nu = L[L.length - 2][1] + 2n;
  if (nu < 34n) continue;
  const z = zoneOf(L);
  if (!z || z.length === 0) continue;
  const digits = [];
  for (const [b, c] of z) for (let r = 0n; r < c; r++) digits.push(SYM[b]);
  // coefficient vector over context-indices
  const MODEL = process.env.MODEL ?? 'left-parity';
  const coef = new Map();
  for (let i = 0; i < digits.length; i++) {
    const pos = digits.length - 1 - i;        // rightmost digit = position 0
    const left = i === 0 ? 'B' : digits[i - 1];
    const right = i === digits.length - 1 ? 'T' : digits[i + 1];
    let ctx;
    if (MODEL === 'left') ctx = `${left}${digits[i]}`;
    else if (MODEL === 'left-parity') ctx = `${left}${digits[i]}${pos % 2}`;
    else if (MODEL === 'right-parity') ctx = `${digits[i]}${right}${pos % 2}`;
    else ctx = `${left}${digits[i]}${right}`;
    const k = idxOf(ctx);
    coef.set(k, (coef.get(k) ?? 0n) + (1n << BigInt(pos)));
  }
  rows.push({ coef, rhs: nu });
}
console.log(`\n${rows.length} equations, ${pairs.length} pair unknowns: ${pairs.join(' ')}`);

// exact Gaussian elimination over rationals (BigInt fractions)
const n = pairs.length;
const gcd = (x, y) => { x = x < 0n ? -x : x; y = y < 0n ? -y : y; while (y) [x, y] = [y, x % y]; return x; };
const frac = (p, q = 1n) => { if (q < 0n) { p = -p; q = -q; } const g = gcd(p, q) || 1n; return [p / g, q / g]; };
const fAdd = ([a, b], [c, d]) => frac(a * d + c * b, b * d);
const fMul = ([a, b], [c, d]) => frac(a * c, b * d);
const fNeg = ([a, b]) => [-a, b];
const mat = [];
for (const r of rows.slice(0, 4000)) {
  const row = new Array(n + 1).fill(null).map(() => [0n, 1n]);
  for (const [k, v] of r.coef) row[k] = [v, 1n];
  row[n] = [r.rhs, 1n];
  mat.push(row);
}
let rank = 0;
const pivCol = [];
for (let col = 0; col < n && rank < mat.length; col++) {
  let p = -1;
  for (let r = rank; r < mat.length; r++) if (mat[r][col][0] !== 0n) { p = r; break; }
  if (p < 0) continue;
  [mat[rank], mat[p]] = [mat[p], mat[rank]];
  const inv = frac(mat[rank][col][1], mat[rank][col][0]);
  for (let c = col; c <= n; c++) mat[rank][c] = fMul(mat[rank][c], inv);
  for (let r = 0; r < mat.length; r++) {
    if (r === rank || mat[r][col][0] === 0n) continue;
    const f = fNeg(mat[r][col]);
    for (let c = col; c <= n; c++) mat[r][c] = fAdd(mat[r][c], fMul(f, mat[rank][c]));
  }
  pivCol.push(col);
  rank++;
}
let inconsistent = 0;
for (let r = rank; r < mat.length; r++) if (mat[r][n][0] !== 0n) inconsistent++;
console.log(`rank ${rank}, inconsistent rows: ${inconsistent}`);

// localize failures: solve from a clean training subset (ν odd, mid-range),
// then classify every anchor by fit and report the failing νs' structure.
{
  let train = rows.filter((_, i) => i % 37 === 0);
  for (let iter = 0; iter < 3; iter++) {
  const M2 = [];
  for (const r of train) {
    const row = new Array(n + 1).fill(null).map(() => [0n, 1n]);
    for (const [k, v] of r.coef) row[k] = [v, 1n];
    row[n] = [r.rhs, 1n];
    M2.push(row);
  }
  let rk = 0; const pc = [];
  for (let col = 0; col < n && rk < M2.length; col++) {
    let p = -1;
    for (let r2 = rk; r2 < M2.length; r2++) if (M2[r2][col][0] !== 0n) { p = r2; break; }
    if (p < 0) continue;
    [M2[rk], M2[p]] = [M2[p], M2[rk]];
    const inv = frac(M2[rk][col][1], M2[rk][col][0]);
    for (let c = col; c <= n; c++) M2[rk][c] = fMul(M2[rk][c], inv);
    for (let r2 = 0; r2 < M2.length; r2++) {
      if (r2 === rk || M2[r2][col][0] === 0n) continue;
      const f = fNeg(M2[r2][col]);
      for (let c = col; c <= n; c++) M2[r2][c] = fAdd(M2[r2][c], fMul(f, M2[rk][c]));
    }
    pc.push(col); rk++;
  }
  const w2 = new Array(n).fill(null);
  for (let r2 = 0; r2 < rk; r2++) w2[pc[r2]] = M2[r2][n];
  const rho2 = (v) => { let r2 = 0; while (v % 2n === 0n && v > 0n) { v /= 2n; r2++; } return r2; };
  const failHist = new Map();
  let pass = 0, fail = 0, unk = 0;
  const failSamples = [];
  const passes = [];
  for (const r of rows) {
    let acc = [0n, 1n], missing = false;
    for (const [k, v] of r.coef) { if (!w2[k]) { missing = true; break; } acc = fAdd(acc, fMul([v, 1n], w2[k])); }
    if (missing) { unk++; continue; }
    if (acc[1] === 1n && acc[0] === r.rhs) { pass++; passes.push(r); }
    else {
      fail++;
      const key = `ρ=${rho2(r.rhs)}`;
      failHist.set(key, (failHist.get(key) ?? 0) + 1);
      if (failSamples.length < 15) failSamples.push(`ν=${r.rhs} (Δ=${acc[1] === 1n ? acc[0] - r.rhs : acc[0] + '/' + acc[1] + '−' + r.rhs})`);
    }
  }
  console.log(`iter ${iter}: pass ${pass}, fail ${fail}, unknown-context ${unk}`);
  if (fail + unk === 0) { console.log('CONVERGED: exact decoder on all anchors'); break; }
  console.log('  fail histogram by ρ(ν):', JSON.stringify([...failHist.entries()].sort()));
  console.log('  fail samples:', failSamples.join('  '));
  train = passes.filter((_, i) => i % 29 === 0);
  }
}
if (!inconsistent) {
  const w = new Array(n).fill(null);
  for (let r = 0; r < rank; r++) w[pivCol[r]] = mat[r][n];
  console.log('solved weights (pair: value):');
  for (let k = 0; k < n; k++) if (w[k]) console.log(`  w(${pairs[k]}) = ${w[k][0]}${w[k][1] !== 1n ? '/' + w[k][1] : ''}`);
  // verify on ALL rows
  let bad = 0;
  for (const r of rows) {
    let acc = [0n, 1n];
    for (const [k, v] of r.coef) { if (!w[k]) { bad++; acc = null; break; } acc = fAdd(acc, fMul([v, 1n], w[k])); }
    if (acc && (acc[1] !== 1n || acc[0] !== r.rhs)) bad++;
  }
  console.log(`verification over all ${rows.length} anchors: ${bad === 0 ? 'ALL EXACT' : bad + ' mismatches'}`);
}

// dump a dyadic neighborhood: around ν = 64..96 (post 2^6 carry region)
for (const [lo, hi] of [[62n, 82n], [126n, 140n], [254n, 268n]]) {
  console.log(`\n--- ν ∈ [${lo}, ${hi}] ---`);
  for (const L of anchors) {
    if (L.length < 3) continue;
    const nu = L[L.length - 2][1] + 2n;
    if (nu < lo || nu > hi) continue;
    console.log(`ν=${String(nu).padStart(5)} (${nu.toString(2).padStart(10)}): ${fmt(L)}`);
  }
}
