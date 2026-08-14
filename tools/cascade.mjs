import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// M3 build 3: the cascade. Walks every remaining calendar moment (events +
// ordinary generation collapses) from the 2^275 collapse to the void:
// seed at moment−12 from the tracked state, run through the moment, parse
// the post-moment left structure and zone length from the observed anchors,
// update state, jump to the next moment. The first four moments reproduce
// the hand-crossed chapters (regression); everything after is new. Ends at
// the moment that fails to parse or fails to anchor — the true finale —
// which it runs long and reports raw. Ledger v2 predictions: P-2026-08-14-k.5.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };
const GLYPH = [10, 14, 11, 15];
const O = 10n, E = 14n, A = 11n, F = 15n;
const fmt = (rs) => rs.map(([b, c]) => `${NAME[Number(b)] ?? Number(b).toString(2)}^${c}`).join(' ');

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
const coalesce = (runs) => {
  const out = [];
  for (const [b, c] of runs) {
    if (c === 0n) continue;
    if (out.length && out[out.length - 1][0] === b) out[out.length - 1][1] += c;
    else out.push([b, c]);
  }
  return out;
};
const zoneRuns = (nu, len) => coalesce(Array.from({ length: len }, (_, j) => [cellGlyph(len - 1 - j, nu), 1n]));
const buildConfig = (leftRuns, nu, len) =>
  coalesce([...leftRuns, ...zoneRuns(nu, len), [F, 1n], [E, nu - 2n], [O, 1n]]);

// moments: calendar events + ordinary collapses (2^m, m≡3 mod 4), ν > start
function moments(startNu, maxK) {
  const ev = [];
  for (let k = 5n; k <= maxK; k++) {
    const p = 1n << k;
    const r = k % 4n;
    if (r === 0n) ev.push([p, 'respell']);
    if (r === 1n) { ev.push([p, 'paycollapse']); ev.push([3n * p, 'pay']); }
    if (r === 2n) { ev.push([p, 'respell']); ev.push([3n * p, 'pay']); ev.push([5n * p, 'borrow']); }
    if (r === 3n) { ev.push([p, 'collapse']); ev.push([3n * p, 'pay']); }
  }
  return ev.filter(([p]) => p > startNu).sort((x, y) => (x[0] < y[0] ? -1 : 1));
}

// parse an observed anchor into {leftRuns, len} given ν, trying len candidates
function parseAnchor(L, nu, lenGuesses) {
  const runs = L.map(([b, c]) => [BigInt(b), c]);
  if (runs.length < 2) return null;
  if (runs[runs.length - 1][0] !== O || runs[runs.length - 1][1] !== 1n) return null;
  if (runs[runs.length - 2][0] !== E) return null;
  for (const len of lenGuesses) {
    const want = coalesce([...zoneRuns(nu, len), [F, 1n], [E, nu - 2n], [O, 1n]]);
    // match want as a suffix of runs, allowing the boundary run to be merged
    if (want.length > runs.length) continue;
    let ok = true, boundaryExtra = null;
    for (let i = 1; i <= want.length; i++) {
      const [wb, wc] = want[want.length - i];
      const [rb, rc] = runs[runs.length - i];
      if (rb !== wb) { ok = false; break; }
      if (i < want.length) { if (rc !== wc) { ok = false; break; } }
      else if (rc === wc) boundaryExtra = null;
      else if (rc > wc) boundaryExtra = [rb, rc - wc];   // leftmost zone run merged with left structure
      else { ok = false; break; }
    }
    if (!ok) continue;
    const leftRuns = runs.slice(0, runs.length - want.length).map(([b, c]) => [b, c]);
    if (boundaryExtra) leftRuns.push(boundaryExtra);
    return { leftRuns: coalesce(leftRuns), len };
  }
  return null;
}
const countBlocks = (runs) => runs.reduce((a, [, c]) => a + c, 0n);

// initial state: entering the 2^275 collapse (post-lastpay, verified ch.1)
let state = {
  leftRuns: [[A, 1n], [E, 1n], [O, 2n], [F, 1n], [O, 2n], [E, 1n]],   // preamble(s=137), 8 cells
  len: 207,
};
const EPS = 12n;
const list = moments(3n * (1n << 273n), 300n);
console.log(`cascade: ${list.length} moments from post-lastpay state (L=${countBlocks(state.leftRuns)}, len=${state.len})`);

for (const [nu, type] of list) {
  const nu0 = nu - EPS;
  const init = { left: buildConfig(state.leftRuns, nu0, state.len).map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n };
  let post = null, stable = 0, anchorsPast = 0, res;
  try {
    res = runMacro(m, 4, {
      maxOps: 60000, macro, init,
      onEdge: (s) => {
        if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
        if (s.ops === 1) return;
        const L = s.left;
        if (L.length < 2) return;
        const nuHere = L[L.length - 2][0] === 14 ? L[L.length - 2][1] + 2n : null;
        if (nuHere === null || nuHere < nu) return;
        anchorsPast++;
        // ledger dictates len: pay grows the zone, borrow shrinks it. Parsing
        // with a free len is ambiguous at O-boundaries and MUST NOT be done —
        // a wrong split rebuilds a counterfeit seed for the next moment.
        const expLen = state.len + (type === 'pay' || type === 'paycollapse' ? 1 : type === 'borrow' ? -1 : 0);
        const parsed = parseAnchor(L, nuHere, [expLen]);
        if (!parsed) { if (!post) post = { fail: true, nu: nuHere, raw: L.map(([b, c]) => [b, c]) }; return; }
        if (!post || post.fail) { post = parsed; return; }
        if (parsed.len === post.len && fmt(parsed.leftRuns) === fmt(post.leftRuns)) stable++;
        if (anchorsPast > 24) throw { done: true };
      },
    });
  } catch (err) {
    if (!err?.done) throw err;
    res = { status: 'early-exit', ops: 0 };
  }
  if (post && !post.fail) {
    const L0 = countBlocks(state.leftRuns), L1 = countBlocks(post.leftRuns);
    console.log(`ν=${type.padEnd(11)} @ ~2^${nu.toString(2).length - 1}  left: [${fmt(state.leftRuns)}] → [${fmt(post.leftRuns)}]  len ${state.len}→${post.len}  L ${L0}→${L1}  total=${L1 + BigInt(post.len)}  stable=${stable}`);
    state = { leftRuns: post.leftRuns, len: post.len };
  } else {
    console.log(`\n=== CASCADE BREAKS at ${type} ν ≈ 2^${nu.toString(2).length - 1} ===`);
    if (post?.fail) console.log(`unparseable anchor at ν=…${post.nu.toString().slice(-10)}:\n  ${fmt(post.raw).slice(0, 400)}`);
    console.log(`run status=${res.status}${res.cert ? ` cert=${res.cert}` : ''} ops=${res.ops} anchors past moment=${anchorsPast}`);
    console.log(`\n=== THE FINALE: running long ===`);
    const res2 = runMacro(m, 4, {
      maxOps: 3e6, macro,
      init: { left: buildConfig(state.leftRuns, nu - EPS, state.len).map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n },
    });
    console.log(`status=${res2.status}${res2.cert ? `  CERT=${res2.cert}` : ''}  ops=${res2.ops}  steps(rel)=${res2.steps}`);
    console.log(`final: ${res2.config}`);
    process.exit(0);
  }
}
console.log('\ncascade walked every moment to k=300 without breaking — the ledger continues; extend maxK');
