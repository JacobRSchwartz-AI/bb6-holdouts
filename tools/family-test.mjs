import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { proveLocal, CONTEXT } from '../src/family.mjs';
import { exprStr } from '../src/symbolic.mjs';

// First context-abstracted lemma on the Odometer: the plain sweep tick.
// From ANY tape content beyond the last two digit runs, one sweep does
// (c, d, N) -> (c+1, d-1, N+1). Proven with c, d, N formal; valid for every
// context because the head never crosses the marker.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

// grab a concrete anchor whose last two digit runs have counts >= 3 and
// its successor anchor, as ground truth
const snaps = [];
runMacro(m, K_BLOCK, {
  maxOps: 300000, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    snaps.push(s.left.map(([b, c]) => [b, c]));
  },
});
let g = -1;
for (let i = 0; i < snaps.length - 1; i++) {
  const L = snaps[i];
  if (L.length >= 6 && L[L.length - 4][1] >= 2n && L[L.length - 5][1] >= 2n &&
      snaps[i + 1].length === L.length) { g = i; break; }
}
if (g < 0) { console.error('no suitable anchor'); process.exit(1); }
const conc = snaps[g], next = snaps[g + 1];
const tail = conc.slice(-5);            // [Bc^c, Bd^d, Bsep^1, BN^N, Btail^1]
console.log('anchor tail:', tail.map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${c}`).join(' '));

// formal params: n0:=c, n1:=d, n2:=N
const X = (j) => ({ c: [0n, 0n, 0n].map((_, i) => (i === j ? 1n : 0n)), b: 0n });
const C3 = (b) => ({ c: [0n, 0n, 0n], b });
const pre = {
  left: [
    [CONTEXT, C3(1n)],
    [tail[0][0], X(0)], [tail[1][0], X(1)], [tail[2][0], C3(tail[2][1])],
    [tail[3][0], X(2)], [tail[4][0], C3(tail[4][1])],
  ],
  right: [],
  q: STATE_C, facing: 'R',
  steps: C3(0n), n0: [1n, 1n, 1n],
};

const r = proveLocal(m, K_BLOCK, macro, pre, {
  until: (s) => s.q === STATE_C && s.facing === 'R' && s.right.length === 0 && s.left.length === pre.left.length,
  maxHops: 8,
  onHop: (h, s) => console.log(`  hop ${h}: q=${s.q} facing=${s.facing} right=${s.right.length} left=` +
    s.left.map(([b, c]) => `${b === CONTEXT ? 'CTX' : b.toString(2).padStart(4, '0')}^${exprStr(c)}`).join(' ')),
});
console.log(`\nresult: ${r.result}`);
if (r.result === 'proved') {
  console.log('post config (counts as expressions over c,d,N = n0,n1,n2):');
  r.state.left.forEach(([b, c]) => console.log(`  ${b === CONTEXT ? 'CONTEXT' : b.toString(2).padStart(4, '0')}^${exprStr(c)}`));
  console.log(`steps = ${exprStr(r.state.steps)}   side conditions: params >= [${r.state.n0.join(',')}]`);

  // ground truth check: evaluate post at the observed (c,d,N)
  const vals = [tail[0][1], tail[1][1], tail[3][1]];
  const ev = (e) => e.c.reduce((a, v, i) => a + v * vals[i], e.b);
  const predicted = r.state.left.slice(1).map(([b, c]) => [b, ev(c)]);
  const actual = next.slice(-predicted.length);
  const ok = predicted.every(([b, c], i) => b === actual[i][0] && c === actual[i][1]);
  console.log(`ground-truth tail match vs next concrete anchor: ${ok ? 'EXACT' : 'MISMATCH'}`);
  process.exit(ok ? 0 : 1);
}
process.exit(1);
