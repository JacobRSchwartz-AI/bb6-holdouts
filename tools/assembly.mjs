import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// The assembly (P-2026-08-14-i): one global clock law for every sweep.
//   steps(ν) = 16·ν + 34 + 6·t + 2·[t even] + 4·[ν+1 = 2^k]   (t = trailing-ones)
// with a finite price list of calendar-event exceptions. Then G(j) by
// summation over the trailing-ones distribution, checked against the
// simulator's exact generation totals.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
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
const MAXNU = [...simSteps.keys()].reduce((a, b) => (a > b ? a : b));
console.log(`${simSteps.size} anchors, ν ≤ ${MAXNU}`);

const trailingOnes = (x) => { let t = 0n; while ((x & 1n) === 1n) { x >>= 1n; t++; } return t; };
const qa = (nu) => { let w = nu + 1n, a = 0n; while (w % 2n === 0n) { w /= 2n; a++; } return [w, a]; };

const base = (nu) => {
  const t = trailingOnes(nu);
  const [q] = qa(nu);
  return 16n * nu + 34n + 6n * t + (t % 2n === 0n ? 2n : 0n) + (q === 1n ? 4n : 0n);
};
const isRespell = (nu) => { const [q, a] = qa(nu); return q === 1n && a % 2n === 0n; };

// pass 1: global law census
let ok = 0, respellN = 0, other = 0;
const exceptions = new Map();   // deviation signature -> [{nu, t, q, a, dev}]
for (let nu = 34n; nu < MAXNU; nu++) {
  const truth = simSteps.get(nu + 1n) - simSteps.get(nu);
  if (isRespell(nu)) {
    const dev = truth - 16n * nu;
    const key = `respell:${dev}`;
    if (!exceptions.has(key)) exceptions.set(key, []);
    exceptions.get(key).push(nu);
    respellN++;
    continue;
  }
  const dev = truth - base(nu);
  if (dev === 0n) { ok++; continue; }
  other++;
  const [q, a] = qa(nu);
  const key = `dev=${dev}|q=${q > 9n ? 'big' : q}|a%4=${a % 4n}`;
  if (!exceptions.has(key)) exceptions.set(key, []);
  exceptions.get(key).push(nu);
}
const total = Number(MAXNU - 34n);
console.log(`\nglobal law: ${ok}/${total} exact (${(100 * ok / total).toFixed(3)}%) | respell sweeps ${respellN} | other deviations ${other}`);
console.log('exception census (signature: count, first few ν):');
for (const [key, nus] of [...exceptions.entries()].sort((a, b) => b[1].length - a[1].length).slice(0, 24)) {
  console.log(`  ${key}: ×${nus.length}  ${nus.slice(0, 5).join(' ')}`);
}

// pass 2: generation totals via the law + measured exceptions
console.log('\nG(j) via summation (law + exception price list) vs simulator:');
for (let j = 6n; j <= 17n; j++) {
  const lo = 1n << j, hi = 1n << (j + 1n);
  let simTotal = 0n, lawTotal = 0n;
  for (let nu = lo; nu < hi; nu++) {
    simTotal += simSteps.get(nu + 1n) - simSteps.get(nu);
    if (isRespell(nu)) lawTotal += simSteps.get(nu + 1n) - simSteps.get(nu);   // priced from list
    else lawTotal += base(nu);
  }
  // add back non-respell deviations (the finite price list)
  let devSum = 0n;
  for (const [key, nus] of exceptions) {
    if (key.startsWith('respell')) continue;
    const dev = BigInt(key.match(/dev=(-?\d+)\|/)[1]);
    for (const nu of nus) if (nu >= lo && nu < hi) devSum += dev;
  }
  const okj = lawTotal + devSum === simTotal;
  console.log(`  j=${j}: ${okj ? 'EXACT' : `MISMATCH Δ=${simTotal - lawTotal - devSum}`}`);
}
