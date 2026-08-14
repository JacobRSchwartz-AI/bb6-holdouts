import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// M3 build 1: the descent ledger. Walks the pay/borrow calendar from the
// structured era to reservoir exhaustion, locates the fatal event (the pay
// that finds the reservoir empty), and prices the whole journey with the
// global clock law — closed-form sums, no per-sweep loop. The closed forms
// are regression-checked against the simulator's exact generation totals
// (j = 6..17) before being trusted out to the bottom.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);

// ---- calendar (identical generator to spell.mjs, unbounded k) ----
function calendarEvents(maxK) {
  const ev = [];
  for (let k = 5n; k <= maxK; k++) {
    const p = 1n << k;
    const r = k % 4n;
    if (r === 0n) ev.push([p, 'respell', k]);
    if (r === 1n) { ev.push([p, 'pay', k]); ev.push([3n * p, 'pay', k]); }
    if (r === 2n) { ev.push([p, 'respell', k]); ev.push([3n * p, 'pay', k]); ev.push([5n * p, 'borrow', k]); }
    if (r === 3n) ev.push([3n * p, 'pay', k]);
  }
  return ev.filter(([p]) => p > 34n).sort((x, y) => (x[0] < y[0] ? -1 : 1));
}

// ---- part A: the ledger ----
const events = calendarEvents(300n);
let R = 202n, len = 5n, s = 0n;
let fatal = null, firstZero = null;
const tail = [];
for (const [nu, type, k] of events) {
  if (type === 'pay') {
    if (R === 0n) { fatal = { nu, k, len, s }; break; }
    len++; R--;
  } else if (type === 'borrow') { len--; R++; }
  else { s = k / 2n; }
  if (R === 0n && !firstZero) firstZero = { nu, type, k };
  tail.push([nu, type, k, R, len, s]);
}
const nuStr = (nu, k) => {
  const q = nu >> k;
  return `${q}·2^${k}`;
};
console.log('=== The descent ledger ===');
console.log(`events walked: ${tail.length}; final 14 before the fatal pay:`);
for (const [nu, type, k, r2, l2, s2] of tail.slice(-14)) {
  console.log(`  ν=${nuStr(nu, k)}  ${type.padEnd(7)}  R=${r2}  len=${l2}  s=${s2}`);
}
console.log(`\nfirst R=0 reached: after ${firstZero.type} at ν=${nuStr(firstZero.nu, firstZero.k)}`);
console.log(`FATAL EVENT: pay at ν* = ${nuStr(fatal.nu, fatal.k)} with R=0`);
console.log(`  ν* = ${fatal.nu}`);
console.log(`  (~10^${fatal.nu.toString().length - 1}); zone len=${fatal.len}, preamble s=${fatal.s} (binary ${fatal.s.toString(2)})`);
console.log(`  the fatal sweep is ν*−1 → ν*: the zone must grow a cell and no reservoir block exists`);

// ---- part B: exact pricing via the global clock ----
// steps(ν) = 16ν + 34 + 6t + 2[t even] + 4[ν+1=2^m], t = trailing-ones(ν);
// only respell sweeps (ν+1 = 2^k, k even) deviate: flat 1680 over 16ν for
// k≡2 mod 4; 1680 + c(r) for k≡0 mod 4, r = trailingOnes(s_old). Observed
// c: r=1→20, r=2→24, r=3→32; primary continuation +4/+8 staircase
// (r=4→36), alternate 16+2^(r+1) (r=4→48) — graded by the j=32 chain.
const TMAX = 300n;
const cntCong = (x, r, mod) => (x <= r ? 0n : (x - r + mod - 1n) / mod);   // #{ν∈[0,x): ν≡r mod m}
const geT = (a, b, T) => cntCong(b, (1n << T) - 1n, 1n << T) - cntCong(a, (1n << T) - 1n, 1n << T);   // #{t(ν) ≥ T}
function sumBase(a, b) {   // Σ base(ν), ν ∈ [a,b), ignoring respell repricing
  let total = 16n * ((a + b - 1n) * (b - a) / 2n) + 34n * (b - a);
  let sumT = 0n;
  for (let T = 1n; T <= TMAX; T++) sumT += geT(a, b, T);
  total += 6n * sumT;
  let evenT = 0n;
  for (let T = 0n; T <= TMAX; T += 2n) evenT += geT(a, b, T) - geT(a, b, T + 1n);
  total += 2n * evenT;
  for (let mm = 1n; (1n << mm) <= b; mm++) {
    const nu = (1n << mm) - 1n;
    if (nu >= a && nu < b) total += 4n;
  }
  return total;
}
const trailingOnes = (x) => { let t = 0n; while ((x & 1n) === 1n) { x >>= 1n; t++; } return t; };
const baseOne = (nu) => {
  const t = trailingOnes(nu);
  let v = 16n * nu + 34n + 6n * t + (t % 2n === 0n ? 2n : 0n);
  let w = nu + 1n; while (w % 2n === 0n) w >>= 1n;
  if (w === 1n) v += 4n;
  return v;
};
// staircase +4/+8: c(1)=20, c(2)=24, c(3)=32, c(4)=36, c(5)=44, c(6)=48 …
const cStair = (r) => 20n + 12n * ((r - 1n) / 2n) + 4n * ((r - 1n) % 2n);
const cGeom = (r) => 16n + (1n << (r + 1n));
function spellSteps(a, b, cFn) {   // exact Σ steps over sweeps ν ∈ [a,b)
  let total = sumBase(a, b);
  for (let k = 6n; (1n << k) <= b; k += 2n) {   // respell sweeps: ν = 2^k − 1, k even
    const nu = (1n << k) - 1n;
    if (nu < a || nu >= b) continue;
    total -= baseOne(nu);
    let price = 16n * nu + 1680n;
    if (k % 4n === 0n) price += cFn(trailingOnes(k / 2n - 1n));
    total += price;
  }
  return total;
}

// regression 1: closed-form sumBase vs direct loop on sample ranges
for (const [a, b] of [[34n, 4000n], [5000n, 70000n], [130000n, 266000n]]) {
  let direct = 0n;
  for (let nu = a; nu < b; nu++) direct += baseOne(nu);
  if (direct !== sumBase(a, b)) { console.log(`sumBase REGRESSION FAIL [${a},${b})`); process.exit(1); }
}
console.log('\nsumBase closed form vs direct loop: 3/3 exact');

// regression 2: spellSteps vs simulator generation totals
const simSteps = new Map();
runMacro(m, 4, {
  maxOps: 4e6, macro,
  onEdge: (st) => {
    if (st.q !== 2 || st.facing !== 'R' || st.right.length !== 0) return;
    const L = st.left;
    if (L.length < 3) return;
    simSteps.set(L[L.length - 2][1] + 2n, st.steps);
  },
});
let genOk = 0, genN = 0;
for (let j = 6n; j <= 17n; j++) {
  const lo = 1n << j, hi = 1n << (j + 1n);
  if (!simSteps.has(lo) || !simSteps.has(hi)) continue;
  genN++;
  const truth = simSteps.get(hi) - simSteps.get(lo);
  if (spellSteps(lo, hi, cStair) === truth) genOk++;
  else console.log(`  gen j=${j}: MISMATCH Δ=${truth - spellSteps(lo, hi, cStair)}`);
}
console.log(`spellSteps vs simulator generation totals: ${genOk}/${genN} exact`);

// the descent total: absolute steps at the start of the fatal sweep
const anchorNu = 1n << 17n;
const anchorSteps = simSteps.get(anchorNu);
const lastSweep = fatal.nu - 1n;   // fatal sweep is lastSweep → ν*; price the journey UP TO its start
const toFatalStair = anchorSteps + spellSteps(anchorNu, lastSweep, cStair);
const toFatalGeom = anchorSteps + spellSteps(anchorNu, lastSweep, cGeom);
const sci = (x) => { const d = x.toString(); return `${d[0]}.${d.slice(1, 6)}e${d.length - 1}`; };
console.log('\n=== The price of the descent ===');
console.log(`absolute steps at SPELL(ν*−1), the start of the fatal sweep:`);
console.log(`  primary (staircase c): ${sci(toFatalStair)}`);
console.log(`  full integer: ${toFatalStair}`);
console.log(`  alternate respell law shifts it by: ${toFatalGeom - toFatalStair} steps (of ~10^${toFatalStair.toString().length - 1})`);
