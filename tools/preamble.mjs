import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { symbolicRun, makeSymbolicState, evalExprAt, exprStr } from '../src/symbolic.mjs';

// Build A: continuous symbolic chain to generation 28, logging the full
// preamble at every M-offset event and every zone collapse. Tests the
// registered predictions P-2026-08-13-a and settles whether the preamble
// register is periodic or drifting.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const N_START = 49150n;
const TARGET_N = 2n ** BigInt(process.argv[2] ?? 28) - 2n;
const SPAN = Number(TARGET_N - N_START);
const M_VAL = 194n;
const STATE_C = 2;

const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

let startSnap = null;
runMacro(m, K_BLOCK, {
  maxOps: 1e6, macro,
  onEdge: (s) => {
    if (startSnap || s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    if (s.left[s.left.length - 2]?.[1] === N_START) {
      startSnap = { ...s, left: s.left.map(([b, c]) => [b, c]), right: [] };
    }
  },
});
if (!startSnap) { console.error('start anchor not found'); process.exit(1); }

const startCounts = startSnap.left.map(([, c]) => c);
const vals = [M_VAL, startCounts[startCounts.length - 2]];
let state = makeSymbolicState(startSnap, [startSnap.left.findIndex(([, c]) => c === M_VAL), startCounts.length - 2]);
const stop = (q, facing) => q === STATE_C && facing === 'R';
const template = (left) => left.map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${exprStr(c)}`).join(' ');

let lastMOffset = 0n;
const t0 = performance.now();
for (let t = 1; t <= SPAN; t++) {
  const r = symbolicRun(m, K_BLOCK, macro, state, { stop, opsCap: 300000 });
  if (r.result !== 'ok') { console.log(`t=${t}: ${r.result} — stopping`); break; }
  state = { left: r.left, right: r.right, q: r.q, facing: r.facing, steps: r.steps, n0: r.n0 };

  const mRun = state.left.findIndex(([, c]) => c.c[0] !== 0n);
  const nRun = state.left.findIndex(([, c]) => c.c[1] !== 0n);
  if (mRun < 0 || nRun < 0) { console.log(`t=${t}: param run vanished — stopping`); break; }
  const N = N_START + BigInt(t);
  const mOffset = state.left[mRun][1].b;
  if (mOffset !== lastMOffset) {
    console.log(`EVENT ${mOffset > lastMOffset ? 'BORROW' : 'PAY'} t=${t} N=${N} N+2=${N + 2n} Moff=${mOffset}`);
    console.log(`  config: ${template(state.left)}`);
    lastMOffset = mOffset;
  }
  const zone = state.left.slice(mRun + 1, nRun - 1);
  if (zone.length === 1 && state.left[nRun - 1][0] === 15) {
    console.log(`COLLAPSE N=${N} zone=${evalExprAt(zone[0][1], vals)} Moff=${mOffset}`);
    console.log(`  config: ${template(state.left)}`);
    console.log(`  steps(M,N)=${exprStr(state.steps)}`);
  }
  if (t % 8388608 === 0) console.log(`  ... t=${t} (${((performance.now() - t0) / 60000).toFixed(1)} min)`);
}
console.log(`\ndone: ${((performance.now() - t0) / 60000).toFixed(1)} min, final n0=[${state.n0.join(',')}]`);
