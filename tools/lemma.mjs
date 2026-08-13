import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro, shapeSignature, formatConfig } from '../src/macro.mjs';
import { symbolicPeriod, ruleStr, exprStr } from '../src/symbolic.mjs';

// Machine-prove period rules for the Odometer's recurring edge shapes.
// Each proven rule is a lemma: config family C(n) reaches C(A·n+d) in
// steps(n) base steps, for all n >= n0.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const maxOps = Number(process.argv[2] ?? 2e6);

const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);
const edges = [];
runMacro(m, K_BLOCK, {
  maxOps, macro,
  onEdge: (s) => { if (edges.length < 2e6) edges.push(s); },
});
console.log(`${edges.length} edge events`);

const bySig = new Map();
for (const s of edges) {
  const sig = shapeSignature(s.left, s.right, s.facing, s.q);
  if (!bySig.has(sig)) bySig.set(sig, []);
  bySig.get(sig).push(s);
}
const counts = (s) => [...s.left.map(([, c]) => c), ...s.right.map(([, c]) => c)];

const top = [...bySig.values()].filter((g) => g.length >= 4).sort((a, b) => b.length - a.length).slice(0, 12);
let proved = 0, failed = 0;
for (const group of top) {
  const [s1, s2, s3] = group.slice(-3);
  const c1 = counts(s1), c2 = counts(s2), c3 = counts(s3);
  const changed = [];
  for (let j = 0; j < c1.length; j++) if (c2[j] - c1[j] !== 0n || c3[j] - c2[j] !== 0n) changed.push(j);
  if (changed.length === 0 || changed.length > 8) { console.log(`\nshape ×${group.length}: ${changed.length} changing counts — skipped`); continue; }
  let paramIdxs = changed;
  let v;
  for (let widen = 0; widen < 5; widen++) {
    v = symbolicPeriod(m, K_BLOCK, macro, s3, paramIdxs, 500000);
    if (v.result !== 'widen' || paramIdxs.length >= 10) break;
    paramIdxs = [...paramIdxs, v.position].sort((a, b) => a - b);
  }
  console.log(`\nshape ×${group.length}: ${formatConfig(s3.left, s3.right, s3.facing, s3.q, K_BLOCK)}`);
  console.log(`  params at positions [${paramIdxs.join(',')}], observed n1=[${paramIdxs.map((j) => counts(s3)[j]).join(',')}]`);
  if (v.result === 'rule') {
    proved++;
    console.log(`  PROVED: ${ruleStr({ A: v.A, d: v.d, n0: v.n0 })}`);
    console.log(`  steps/period = ${exprStr(v.steps)}  (macro ops in period: ${v.ops})`);
  } else {
    failed++;
    console.log(`  ${v.result}${v.position !== undefined ? ' @pos ' + v.position : ''}`);
  }
}
console.log(`\n${proved} lemmas proved, ${failed} failed`);
