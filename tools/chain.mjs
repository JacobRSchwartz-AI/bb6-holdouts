import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro, formatConfig } from '../src/macro.mjs';
import { symbolicRun, makeSymbolicState, evalExprAt, exprStr } from '../src/symbolic.mjs';

// Machine-verify one full epoch of the Odometer with M and N symbolic.
// Chain: symbolic anchor-to-anchor transitions, cross-checked against the
// concrete trace at every anchor. Success = theorem: for all M >= m0, from
// the epoch-start config the machine reaches the next epoch-start config
// with M-1, N+span, in steps affine in (M, N).
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const N_START = BigInt(process.argv[2] ?? 49150);   // epoch 13 start (K=13, M=194)
const SPAN = Number(process.argv[3] ?? 16384);      // anchor visits in the epoch
const M_VAL = BigInt(process.argv[4] ?? 194);
const STATE_C = 2;

const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

// Pass 1: concrete anchors for the target window (start snapshot + checks).
const anchors = [];
let startSnap = null;
runMacro(m, K_BLOCK, {
  maxOps: 5e6, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    const N = s.left[s.left.length - 2]?.[1];
    if (N === undefined || N < N_START || N > N_START + BigInt(SPAN)) return;
    const snap = { ...s, left: s.left.map(([b, c]) => [b, c]), right: [] };
    if (N === N_START && !startSnap) startSnap = snap;
    anchors.push(snap);
  },
});
if (!startSnap) { console.error('start anchor not found'); process.exit(1); }
console.log(`captured ${anchors.length} concrete anchors from N=${N_START}`);
console.log(`start: ${formatConfig(startSnap.left, startSnap.right, startSnap.facing, startSnap.q, K_BLOCK)}`);

const counts = (s) => s.left.map(([, c]) => c);
const startCounts = counts(startSnap);
const mPos = startCounts.findIndex((c) => c === M_VAL);
const nPos = startCounts.length - 2;
if (mPos < 0 || startCounts.filter((c) => c === M_VAL).length !== 1) { console.error('M run not unique'); process.exit(1); }
console.log(`M at run ${mPos} (=${M_VAL}), N at run ${nPos} (=${startCounts[nPos]}); params n0:=M, n1:=N`);

const concrete = [M_VAL, startCounts[nPos]];
let state = makeSymbolicState(startSnap, [mPos, nPos]);
const stop = (q, facing) => q === STATE_C && facing === 'R';

let mismatches = 0;
const t0 = performance.now();
for (let t = 1; t <= SPAN; t++) {
  const r = symbolicRun(m, K_BLOCK, macro, state, { stop, opsCap: 200000 });
  if (r.result !== 'ok') {
    console.log(`transition ${t}: ${r.result} — chain broken`);
    process.exit(1);
  }
  state = { left: r.left, right: r.right, q: r.q, facing: r.facing, steps: r.steps, n0: r.n0 };
  const conc = anchors[t];
  if (conc) {
    const sym = state.left.map(([b, c]) => [b, evalExprAt(c, concrete)]);
    const ref = conc.left;
    const same = sym.length === ref.length && sym.every(([b, c], i) => b === ref[i][0] && c === ref[i][1]);
    if (!same && mismatches++ < 3) {
      console.log(`MISMATCH at transition ${t}:`);
      console.log(`  sym : [${sym.map(([b, c]) => c).join(',')}]`);
      console.log(`  conc: [${ref.map(([, c]) => c).join(',')}]`);
    }
  }
  if (t % 4096 === 0) console.log(`  t=${t} runs=${state.left.length} n0=[${state.n0.join(',')}] (${((performance.now() - t0) / 1000).toFixed(1)}s)`);
}

console.log(`\nchain of ${SPAN} transitions complete, ${mismatches} mismatches`);
console.log(`final: ${formatConfig(state.left, state.right, state.facing, state.q, K_BLOCK)}`);
console.log(`final counts as expressions:`);
state.left.forEach(([b, c], i) => console.log(`  run ${i}: block=${b.toString(2).padStart(4, '0')} count=${exprStr(c)}`));
console.log(`steps(M,N) = ${exprStr(state.steps)}   for all (M,N) >= [${state.n0.join(',')}]`);
console.log(`check: steps at (${M_VAL}, ${N_START}) = ${evalExprAt(state.steps, concrete)}`);
