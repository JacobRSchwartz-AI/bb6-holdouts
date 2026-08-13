import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { proveLocal, CONTEXT } from '../src/family.mjs';
import { exprStr } from '../src/symbolic.mjs';

// Harvest the phase automaton of the Odometer's low-digit region: walk
// context-abstracted sweeps, one hop per anchor, until the local shape
// recurs (a cycle). Params: n0 = high digit run count, n1 = N. The cycle
// composed = the mid-epoch workhorse lemma C(n0, N) -> C(n0-drain, N+len).
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

// mature anchor: large N, high digit run with count >= 40 to survive a while
const snaps = [];
runMacro(m, K_BLOCK, {
  maxOps: 2e6, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    snaps.push(s.left.map(([b, c]) => [b, c]));
  },
});
let pick = null;
for (const L of snaps) {
  if (L.length < 10) continue;
  const nVal = L[L.length - 2][1];
  if (nVal < 50000n) continue;
  for (let i = L.length - 5; i >= 2 && i >= L.length - 12; i--) {
    if (L[i][0] === 10 && L[i][1] >= 6n) { pick = { L, i }; break; }
  }
  if (pick) break;
}
if (!pick) { console.error('no mature anchor with big digit run'); process.exit(1); }
const { L, i } = pick;
console.log(`window: runs ${i}..${L.length - 1} of ${L.length}; high run 1010^${L[i][1]}, N=${L[L.length - 2][1]}`);

const X = (j) => ({ c: [0n, 0n].map((_, k) => (k === j ? 1n : 0n)), b: 0n });
const C2 = (b) => ({ c: [0n, 0n], b });
const left = [[CONTEXT, C2(1n)]];
for (let p = i; p < L.length; p++) {
  if (p === i) left.push([L[p][0], X(0)]);
  else if (p === L.length - 2) left.push([L[p][0], X(1)]);
  else left.push([L[p][0], C2(L[p][1])]);
}
const pre = { left, right: [], q: STATE_C, facing: 'R', steps: C2(0n), n0: [1n, 1n] };

const keyOf = (s) => s.left.map(([b, c]) => `${b}:${c.c[0]},${c.c[1]}${c.c[0] === 0n && c.c[1] === 0n ? ':' + c.b : ''}`).join(' ');
const seen = new Map([[keyOf(pre), { hop: 0, state: pre }]]);
let cycle = null;

const r = proveLocal(m, K_BLOCK, macro, pre, {
  maxHops: 400,
  until: () => false,
  onHop: (h, s) => {
    const key = keyOf(s);
    if (seen.has(key) && !cycle) cycle = { from: seen.get(key), to: { hop: h + 1, state: s } };
    else seen.set(key, { hop: h + 1, state: s });
  },
});

if (cycle) {
  const a = cycle.from, b = cycle.to;
  console.log(`\nCYCLE: shape at hop ${a.hop} recurs at hop ${b.hop} (length ${b.hop - a.hop})`);
  console.log(`shape: ${a.state.left.map(([bl, c]) => `${bl === CONTEXT ? 'CTX' : bl.toString(2).padStart(4, '0')}^${exprStr(c)}`).join(' ')}`);
  console.log(`  -> : ${b.state.left.map(([bl, c]) => `${bl === CONTEXT ? 'CTX' : bl.toString(2).padStart(4, '0')}^${exprStr(c)}`).join(' ')}`);
  const dSteps = { c: b.state.steps.c.map((v, k) => v - a.state.steps.c[k]), b: b.state.steps.b - a.state.steps.b };
  console.log(`steps per cycle = ${exprStr(dSteps)}; side conds params >= [${b.state.n0.join(',')}]`);
} else {
  console.log(`\nno cycle in 400 hops (${seen.size} distinct shapes); last result: ${r.result}`);
}
