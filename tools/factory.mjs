import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { symbolicRun, makeSymbolicState, evalExprAt, exprStr } from '../src/symbolic.mjs';

// Continuous symbolic chain across many epochs. Logs epoch boundaries (zone
// collapse), M-payment moments (n0 offset changes), and per-boundary configs.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const N_START = BigInt(process.argv[2] ?? 49150);
const SPAN = Number(process.argv[3] ?? 400000);
const M_VAL = BigInt(process.argv[4] ?? 194);
const CONC_OPS = Number(process.argv[5] ?? 8e6);
const STATE_C = 2;

const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

const concrete = [];
let startSnap = null;
runMacro(m, K_BLOCK, {
  maxOps: CONC_OPS, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    const N = s.left[s.left.length - 2]?.[1];
    if (N === undefined || N < N_START || N > N_START + BigInt(SPAN)) return;
    const t = Number(N - N_START);
    concrete[t] = s.left.map(([b, c]) => [b, c]);
    if (t === 0 && !startSnap) startSnap = { ...s, left: s.left.map(([b, c]) => [b, c]), right: [] };
  },
});
if (!startSnap) { console.error('start anchor not found'); process.exit(1); }
const concMax = concrete.length - 1;
console.log(`concrete anchors available through t=${concMax}`);

const startCounts = startSnap.left.map(([, c]) => c);
const mPos = startCounts.findIndex((c) => c === M_VAL);
const nPos = startCounts.length - 2;
const vals = [M_VAL, startCounts[nPos]];
let state = makeSymbolicState(startSnap, [mPos, nPos]);
const stop = (q, facing) => q === STATE_C && facing === 'R';

const findParamRun = (left, j) => left.findIndex(([, c]) => c.c[j] !== 0n);
let lastMOffset = 0n;
let mismatches = 0;
const boundaries = [];
const t0 = performance.now();

for (let t = 1; t <= SPAN; t++) {
  const r = symbolicRun(m, K_BLOCK, macro, state, { stop, opsCap: 300000 });
  if (r.result !== 'ok') { console.log(`t=${t}: ${r.result} — stopping`); break; }
  state = { left: r.left, right: r.right, q: r.q, facing: r.facing, steps: r.steps, n0: r.n0 };

  if (t <= concMax && concrete[t]) {
    const ref = concrete[t];
    const sym = state.left;
    const same = sym.length === ref.length && sym.every(([b, c], i) => b === ref[i][0] && evalExprAt(c, vals) === ref[i][1]);
    if (!same && mismatches++ < 3) console.log(`MISMATCH at t=${t}`);
  }

  const mRun = findParamRun(state.left, 0);
  const nRun = findParamRun(state.left, 1);
  if (mRun < 0 || nRun < 0) { console.log(`t=${t}: param run vanished (m@${mRun} n@${nRun}) — stopping`); break; }
  const mOffset = state.left[mRun][1].b;
  if (mOffset !== lastMOffset) {
    console.log(`t=${t} (N=${N_START + BigInt(t)}): M offset ${lastMOffset} -> ${mOffset}`);
    lastMOffset = mOffset;
  }
  const zone = state.left.slice(mRun + 1, nRun - 1);
  if (zone.length === 1 && state.left[nRun - 1][0] === 15) {
    boundaries.push({
      t, N: N_START + BigInt(t), zoneCount: evalExprAt(zone[0][1], vals), mOffset,
      template: state.left.map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${exprStr(c)}`).join(' '),
      steps: state.steps,
    });
  }
  if (t % 65536 === 0) console.log(`  t=${t} (${((performance.now() - t0) / 1000).toFixed(1)}s) runs=${state.left.length}`);
}

console.log(`\n${mismatches} mismatches vs concrete (checked through t=${Math.min(concMax, SPAN)})`);
console.log(`final n0 lower bounds: [${state.n0.join(',')}]`);
console.log(`\n${boundaries.length} zone-collapse anchors:`);
for (const b of boundaries) {
  console.log(`  t=${b.t} N=${b.N} zone=${b.zoneCount} Moff=${b.mOffset}`);
  console.log(`    ${b.template}`);
  console.log(`    steps(M,N)=${exprStr(b.steps)}`);
}
