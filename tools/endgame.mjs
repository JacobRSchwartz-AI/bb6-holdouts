import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro, formatConfig } from '../src/macro.mjs';

// M3 build 2: the endgame. Seeds the concrete simulator from SPELL-built
// configurations (runMacro init) and crosses the descent's critical moments:
//   validate    — in-range: seed SPELL(ν) at sampled anchors + every event
//                 neighborhood, run one sweep, compare config and steps to
//                 the simulator's ground truth.
//   lastpay     — ν = 3·2^273: the pay that drains the reservoir to R=0.
//   collapse    — ν = 2^275: the full-depth carry with no reservoir.
//   fatal [x]   — ν* = 3·2^274: the pay with nothing to pay with.
//                 x ∈ {e,a,f} spells preamble c6 (bit7 of s=137, dialect
//                 unobserved — run all three, fate should be invariant).
// Predictions for lastpay/collapse/fatal are registered as P-2026-08-14-j
// in notes/odometer.md §3.1 before first run.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };
const GLYPH = [10, 14, 11, 15];
const O = 10n, E = 14n, A = 11n, F = 15n;
const fmt = (rs) => rs.map(([b, c]) => `${NAME[Number(b)] ?? Number(b).toString(2)}^${c}`).join(' ');

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
  if (state.R > 0n) runs.push([state.font, state.R]);
  for (let i = state.len - 1; i >= 0; i--) runs.push([cellGlyph(i, nu), 1n]);
  runs.push([F, 1n]); runs.push([E, nu - 2n]); runs.push([O, 1n]);
  const out = [];
  for (const [b, c] of runs) {
    if (out.length && out[out.length - 1][0] === b) out[out.length - 1][1] += c;
    else out.push([b, c]);
  }
  return out;
}
// preamble numeral of s (P-2026-08-14-d cell laws); c4..c6 = bits ≥ 4,
// dialect unobserved — xGlyph spells a lit high bit-cell.
function preambleOf(s, xGlyph, markC0 = false) {
  const bit = (i) => (s >> BigInt(i)) & 1n;
  const cells = [
    markC0 ? A : bit(0) ? E : O,          // c0 (markC0: carry-out mark from an R=0 collapse, e→a)
    bit(1) ? A : O,                       // c1
    BigInt(GLYPH[Number((s >> 1n) & 3n)]),// c2
    bit(3) ? F : O,                       // c3
    bit(4) || bit(5) ? xGlyph : O,        // c4
    bit(6) ? xGlyph : O,                  // c5
    bit(7) ? xGlyph : O,                  // c6
  ];
  const runs = [[A, 1n]];
  for (let i = 6; i >= 0; i--) {
    const b = cells[i];
    if (runs[runs.length - 1][0] === b) runs[runs.length - 1][1]++;
    else runs.push([b, 1n]);
  }
  return runs;
}
const runsEq = (x, y) => x.length === y.length && x.every(([b, c], i) => BigInt(y[i][0]) === b && BigInt(y[i][1]) === c);

const mode = process.argv[2] ?? 'validate';

if (mode === 'validate') {
  const anchors = new Map(), stepsAt = new Map();
  runMacro(m, 4, {
    maxOps: 4e6, macro,
    onEdge: (s) => {
      if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
      const L = s.left;
      if (L.length < 6) return;
      const nu = L[L.length - 2][1] + 2n;
      anchors.set(nu, L.map(([b, c]) => [b, c]));
      stepsAt.set(nu, s.steps);
    },
  });
  const maxNu = [...anchors.keys()].reduce((a, b) => (a > b ? a : b));
  const targets = new Set();
  for (let nu = 101n; nu < maxNu - 1n; nu += 997n) targets.add(nu);
  for (const [p] of calendarEvents(20n)) {
    for (let d = -8n; d <= 8n; d++) {
      const nu = p + d;
      if (nu >= 34n && nu < maxNu - 1n) targets.add(nu);
    }
  }
  for (let k = 6n; (1n << k) < maxNu - 1n; k++) targets.add((1n << k) - 1n);   // collapse sweeps
  let ok = 0, n = 0;
  const fails = [];
  for (const nu of [...targets].sort((a, b) => (a < b ? -1 : 1))) {
    if (!anchors.has(nu) || !anchors.has(nu + 1n)) continue;
    n++;
    let hit = null;
    try {
      runMacro(m, 4, {
        maxOps: 4000, macro,
        init: { left: anchors.get(nu).map(([b, c]) => [b, c]), right: [], facing: 'R', q: 2, steps: 0n },
        onEdge: (s) => {
          if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
          if (s.ops === 1) return;   // the seed itself
          hit = { left: s.left.map(([b, c]) => [b, c]), steps: s.steps };
          throw { seededAnchor: true };
        },
      });
    } catch (err) { if (!err?.seededAnchor) throw err; }
    const want = anchors.get(nu + 1n);
    const wantSteps = stepsAt.get(nu + 1n) - stepsAt.get(nu);
    const good = hit && hit.left.length === want.length
      && hit.left.every(([b, c], i) => b === want[i][0] && c === want[i][1])
      && hit.steps === wantSteps;
    if (good) ok++;
    else if (fails.length < 10) fails.push({ nu, got: hit ? `${fmt(hit.left)} steps=${hit.steps}` : 'no anchor reached', want: `${fmt(want)} steps=${wantSteps}` });
  }
  console.log(`seeded one-sweep validation: ${ok}/${n} exact (config + steps)`);
  for (const f of fails) console.log(`ν=${f.nu}\n  got : ${f.got}\n  want: ${f.want}`);
  process.exit(ok === n ? 0 : 1);
}

// ---- endgame seeds ----
const xGlyph = { e: E, a: A, f: F }[process.argv[3] ?? 'e'];
const S137 = preambleOf(137n, xGlyph);
const S137marked = preambleOf(137n, xGlyph, true);   // post-2^275-collapse: carry-out mark on c0
const SEEDS = {
  lastpay: {
    nu0: 3n * (1n << 273n) - 12n,
    state: { preamble: S137, font: A, R: 1n, len: 207 - 1, eraStart: 0n },
    event: 3n * (1n << 273n), post: { R: 0n, len: 207 }, sweeps: 40n, maxOps: 200000,
  },
  collapse: {
    nu0: (1n << 275n) - 12n,
    state: { preamble: S137, font: A, R: 0n, len: 207, eraStart: 0n },
    event: 1n << 275n, post: { R: 0n, len: 207 }, postPreamble: S137marked, sweeps: 40n, maxOps: 200000,
  },
  fatal: {
    nu0: 3n * (1n << 274n) - 12n,
    state: { preamble: S137marked, font: A, R: 0n, len: 207, eraStart: 0n },
    event: 3n * (1n << 274n), post: null, sweeps: 4000n, maxOps: 2000000,
  },
  // chapters 2+ (P-2026-08-14-k): each seed's state = previous chapter's
  // observed post-event structure. P7 = post-fatal preamble (c0 consumed).
  respell276: {
    nu0: (1n << 276n) - 12n,
    state: { preamble: [[A, 1n], [E, 1n], [O, 2n], [F, 1n], [O, 2n]], font: A, R: 0n, len: 208, eraStart: 0n },
    event: 1n << 276n, post: null, sweeps: 40n, maxOps: 200000,
  },
  // post-respell276 left context (observed): a e O O f O f
  borrow274: {
    nu0: 5n * (1n << 274n) - 12n,
    state: { preamble: [[A, 1n], [E, 1n], [O, 2n], [F, 1n], [O, 1n], [F, 1n]], font: A, R: 0n, len: 208, eraStart: 0n },
    event: 5n * (1n << 274n), post: null, sweeps: 40n, maxOps: 200000,
  },
};
const seed = SEEDS[mode];
if (!seed) { console.log(`unknown mode ${mode}`); process.exit(1); }

console.log(`=== ${mode} (preamble c6 = ${NAME[Number(xGlyph)]}) ===`);
console.log(`seed ν0 = event − ${seed.event - seed.nu0}; event at ν = ${seed.event.toString().slice(0, 12)}…e${seed.event.toString().length - 1}`);
const init = { left: spell(seed.nu0, seed.state).map(([b, c]) => [b, c]), right: [], facing: 'R', q: 2, steps: 0n };
console.log(`seed config: ${fmt(init.left.slice(0, 10))} … [zone] … ${fmt(init.left.slice(-3))}  (${init.left.length} runs)`);

let anchorsSeen = 0n, lastNu = null, firstBad = null, postChecked = 0, postOk = 0, prevSteps = null;
const postState = seed.post ? { preamble: seed.postPreamble ?? S137, font: seed.state.font, R: seed.post.R, len: seed.post.len } : null;
const res = runMacro(m, 4, {
  maxOps: seed.maxOps, macro, init,
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    if (s.ops === 1) return;
    anchorsSeen++;
    const L = s.left;
    const nu = L.length >= 3 ? L[L.length - 2][1] + 2n : null;
    if (nu !== null && nu >= seed.event - 1n && nu <= seed.event + 2n) {
      if (prevSteps !== null) console.log(`sweep into ν=…${nu.toString().slice(-8)}: steps=${s.steps - prevSteps}`);
    }
    if (nu !== null && nu >= seed.event - 2n && nu <= seed.event + 2n) prevSteps = s.steps;
    else prevSteps = null;
    lastNu = nu;
    const st = nu !== null && nu >= seed.event && postState ? postState : seed.state;
    if (nu !== null && (nu < seed.event || postState)) {
      const want = spell(nu, st);
      const good = L.length === want.length && L.every(([b, c], i) => BigInt(b) === want[i][0] && c === want[i][1]);
      if (postState && nu >= seed.event) { postChecked++; if (good) postOk++; }
      if (!good && !firstBad) firstBad = { nu, got: fmt(L), want: fmt(want) };
    }
    if (anchorsSeen <= 3n || (nu !== null && nu >= seed.event - 2n && nu <= seed.event + 3n)) {
      console.log(`anchor ν=${nu !== null ? '…' + nu.toString().slice(-8) : '?'}  runs=${L.length}  left-edge: ${fmt(L.slice(0, 9))}`);
    }
  },
});
console.log(`\nresult: ${res.status}  ops=${res.ops}  anchors seen=${anchorsSeen}`);
if (res.status === 'halt') console.log(`*** HALT at seeded step ${res.steps} ***`);
if (res.status === 'nonhalt') console.log(`*** NONHALT certificate: ${res.cert} ***`);
if (lastNu !== null) console.log(`last anchor ν (tail count+2): …${lastNu.toString().slice(-12)} (Δ from event: ${lastNu - seed.event})`);
if (postState) console.log(`post-event anchors matching predicted SPELL: ${postOk}/${postChecked}`);
if (firstBad) console.log(`first SPELL mismatch at ν=…${firstBad.nu.toString().slice(-10)}\n  got : ${firstBad.got.slice(0, 300)}\n  want: ${firstBad.want.slice(0, 300)}`);
else if (mode !== 'fatal') console.log('all checked anchors matched SPELL exactly');
console.log(`final config: ${res.config}`);
