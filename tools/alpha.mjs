import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// M2d-3: α-preservation.
// Value semantics (redundant binary): digit VALUES O=0, e=1, f=1, a=2
// (e/f distinguish spelling phase, not value; a is the borrow debt = a
// literal 2-digit). With the window seeing zone positions p0..p_m, the
// decoded window value satisfies  v̂ ≡ ν (mod 2^(m+1)).
// Part 1 validates this congruence on every concrete anchor.
// Part 2 checks every book lemma implements +1 (mod the shared window
// modulus) at sampled parameter values, bucketing carry-out cases.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);
const CONTEXT = -1;
const SYMBOL = { 0b1010: 0n, 0b1110: 1n, 0b1011: 2n, 0b1111: 3n };   // O,e,a,f
const deepVal = (s) => (s === 0n ? 0n : s === 2n ? 2n : 1n);          // e,f→1; a→2 (debt)

// Decode a run list (window or full config) ending in the anchor tail.
// Returns {value, positions} where value = Σ val·2^pos over visible zone
// digits read right-to-left, phase cells included via their values
// (p1 f-cell = odd bit: f=1 at p1 contributes 2^0? — no: the phase pair
// (p1,p0) encodes bit0 in p1's value: odd ν ⇔ p1 = f. We fold every
// digit uniformly: bit contribution val·2^(digit index) with index
// counted from p0 = index 0. The sliding cells then hold ⌊v/2⌋ mod 4 and
// ⌊v/4⌋ mod 4 whose VALUES overlap-sum correctly: p2·2 + p3·4 double
// counts the shared bit... so uniform folding is wrong for p2/p3.
// Correct fold (validated below): v̂ = val(p1)·1 + val(p2)·2 + val(p3)·4
// + Σ_{i≥4} val(p_i)·2^(i−?) ... calibrated by Part 1.
function decode(runs, mode) {
  const L = runs.length;
  if (L < 4) return null;
  if (runs[L - 1][0] !== 0b1010 || runs[L - 2][0] !== 0b1110 || runs[L - 3][0] !== 0b1111) return null;
  const digits = [];   // right-to-left, one SYMBOL per digit block
  for (let i = L - 4; i >= 0; i--) {
    const [b, c] = runs[i];
    if (b === CONTEXT || SYMBOL[b] === undefined || c >= 60n) break;
    for (let r = 0n; r < c; r++) digits.push(SYMBOL[b]);
  }
  if (digits.length < 2) return null;
  // p0 = digits[0] (always 0 observed), p1 = digits[1] (bit0 via value),
  // p2 = digits[2] (⌊v/2⌋ mod 4), p3 = digits[3] (⌊v/4⌋ mod 4),
  // deeper = plain bits (val 0/1) or debt (2).
  let v = 0n;
  const mLen = digits.length;
  if (mode === 'overlap') {
    // bit0 from p1 (odd ⇔ val(p1)=1? observed f=1... but f val 1; O val 0)
    const bit0 = digits[1] === 0n ? 0n : 1n;
    const s2 = digits.length > 2 ? digits[2] : 0n;   // symbol = ⌊v/2⌋ mod 4
    const s3 = digits.length > 3 ? digits[3] : 0n;   // symbol = ⌊v/4⌋ mod 4
    const bit1 = s2 & 1n;
    v = bit0 + 2n * bit1 + 4n * s3;                  // s3 supplies bits 2..3
    for (let i = 4; i < digits.length; i++) v += deepVal(digits[i]) << BigInt(i);
    // the top visible digit may hold a debt (value 2) whose high half
    // overflows its own position — trust the congruence only below it
    return { v, bits: Math.min(mLen - 1, 64) };
  }
  return null;
}

const anchors = [];
runMacro(m, K_BLOCK, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    anchors.push(s.left.map(([b, c]) => [b, c]));
  },
});

let tested = 0, exact = 0;
const failByMod = new Map();
const failSamples = [];
for (const L of anchors) {
  if (L.length < 6) continue;
  const nu = L[L.length - 2][1] + 2n;
  if (nu < 34n) continue;
  const d = decode(L, 'overlap');
  if (!d) continue;
  tested++;
  const mod = 1n << BigInt(d.bits);
  if (((nu - d.v) % mod + mod) % mod === 0n) exact++;
  else {
    failByMod.set(d.bits, (failByMod.get(d.bits) ?? 0) + 1);
    if (failSamples.length < 10) failSamples.push(`ν=${nu} v̂=${d.v} bits=${d.bits} νmod=${nu % mod}`);
  }
}
console.log(`Part 1 — value congruence v̂ ≡ ν (mod 2^visible): ${exact}/${tested} anchors exact`);
if (exact !== tested) {
  console.log('  fails by visible-bit count:', JSON.stringify([...failByMod.entries()].sort((a, b) => a[0] - b[0])));
  console.log('  samples:', failSamples.join('  '));
}
