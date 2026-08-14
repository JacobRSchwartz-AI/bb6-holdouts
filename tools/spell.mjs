import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// SPELL(ν) — the complete tape-spelling function (P-2026-08-14-b), and its
// validation against every concrete anchor. SPELL(ν) = preamble(era) ·
// resFont^R(ν) · zone(ν) · f^1 e^(ν−2) O^1, RLE-coalesced. Zone glyphs are
// the pure lattice; zone length and R follow the pay/borrow calendar;
// reservoir font flips at even-k respells; the preamble is a finite
// per-respell-era table (extracted once below, printed for the notes).
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };
const GLYPH = [10, 14, 11, 15];   // window value 0..3 -> O,e,a,f
const O = 10n, E = 14n, A = 11n, F = 15n;

// calendar: k≡0 respell a→e @2^k; k≡1 pay @2^k,3·2^k; k≡2 respell e→a @2^k,
// pay @3·2^k, borrow @5·2^k; k≡3 pay @3·2^k. Structured era starts ν=34.
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

function cellGlyph(i, nu) {
  if (i === 0) return 10n;
  const r = (i - 1) % 3;
  if (r === 0) {
    const s = i === 1 ? 0n : BigInt(4 * ((i - 4) / 3) + 4);
    return ((nu >> s) & 1n) === 1n ? 15n : 10n;
  }
  const mt = r === 1 ? (i - 2) / 3 : (i - 3) / 3;
  const s = BigInt(4 * mt + r);
  return BigInt(GLYPH[Number((nu >> s) & 3n)]);
}

function spell(nu, state) {
  const runs = [];
  for (const [b, c] of state.preamble) runs.push([b, c]);
  runs.push([state.font, state.R]);
  for (let i = state.len - 1; i >= 0; i--) runs.push([cellGlyph(i, nu), 1n]);
  runs.push([F, 1n]); runs.push([E, nu - 2n]); runs.push([O, 1n]);
  const out = [];
  for (const [b, c] of runs) {
    if (out.length && out[out.length - 1][0] === b) out[out.length - 1][1] += c;
    else out.push([b, c]);
  }
  return out;
}

const fmt = (rs) => rs.map(([b, c]) => `${NAME[Number(b)] ?? b.toString(2)}^${c}`).join(' ');

const anchors = [];
runMacro(m, 4, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    anchors.push(s.left.map(([b, c]) => [b, c]));
  },
});

const maxNu = anchors[anchors.length - 1][anchors[anchors.length - 1].length - 2][1] + 2n;
const events = calendarEvents(maxNu);
const state = { preamble: null, font: E, R: 202n, len: 5, eraStart: 34n };
let evIdx = 0;
const preambles = [];   // [eraStartNu, runs] extracted at each respell
let tested = 0, exact = 0;
const fails = [];

for (const L of anchors) {
  if (L.length < 6) continue;
  const nu = L[L.length - 2][1] + 2n;
  if (nu < 34n) continue;
  while (evIdx < events.length && events[evIdx][0] <= nu) {
    const [, type] = events[evIdx++];
    if (type === 'pay') { state.len++; state.R -= 1n; }
    else if (type === 'borrow') { state.len--; state.R += 1n; }
    else { state.font = state.font === E ? A : E; state.preamble = null; }
  }
  if (state.preamble === null) {
    // extract the preamble once per respell era: runs left of the reservoir
    // (leftmost run with count ≥ 60)
    const cut = L.findIndex(([, c]) => c >= 60n);
    state.preamble = L.slice(0, cut).map(([b, c]) => [BigInt(b), BigInt(c)]);
    preambles.push([nu, state.preamble]);
  }
  tested++;
  const want = spell(nu, state);
  const ok = want.length === L.length && want.every(([b, c], i) => BigInt(L[i][0]) === b && BigInt(L[i][1]) === c);
  if (ok) exact++;
  else if (fails.length < 20) fails.push({ nu, got: fmt(L), want: fmt(want) });
}

console.log(`SPELL(ν) validation: ${exact}/${tested} anchors exact (ν ∈ [34, ${maxNu}])`);
console.log(`\npreamble table (${preambles.length} respell eras):`);
for (const [nu, p] of preambles) console.log(`  from ν=${nu}: ${fmt(p)}`);
if (fails.length) {
  console.log(`\nfirst ${fails.length} mismatches:`);
  for (const f of fails) {
    console.log(`ν=${f.nu}\n  got : ${f.got}\n  want: ${f.want}`);
  }
}
