import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { applyBook, konstE } from '../src/compose.mjs';

// Regression for the composition calculus: starting from an early concrete
// anchor, advance by LEMMA APPLICATION ONLY (applyBook — affine algebra,
// no tape simulation) and require exact agreement with the concrete
// simulator at every anchor. Run AFTER tools/lift.mjs has written
// data/book.json.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

const raw = JSON.parse(readFileSync('data/book.json', 'utf8'));
const deE = (e) => ({ c: e.c.map(BigInt), b: BigInt(e.b) });
const book = raw.map((l) => ({
  ...l,
  counts: l.counts.map(BigInt),
  post: l.post.map(([b, e]) => [b, deE(e)]),
  steps: deE(l.steps),
  n0: l.n0.map(BigInt),
}));
console.log(`book: ${book.length} lemmas`);

const anchors = [];
runMacro(m, K_BLOCK, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    anchors.push(s.left.map(([b, c]) => [b, c]));
  },
});
console.log(`${anchors.length} anchors (ground truth)`);

// Transitions 0..4 are the concrete birth base case (incl. the N=2 sweep
// that has no lemma); the formal proof replays them by direct simulation.
// Composition takes over from anchor 5.
const START = 5;
let cfg = {
  runs: anchors[START].map(([b, c]) => [b, konstE(0, c)]),
  steps: konstE(0, 0n),
  n0: [],
};
let ok = 0, fail = null;
for (let i = START; i < anchors.length - 1; i++) {
  const r = applyBook(cfg, book);
  if (r.result !== 'ok') { fail = { i, why: r.result }; break; }
  cfg = r.config;
  const truth = anchors[i + 1];
  const got = cfg.runs;
  const match = got.length === truth.length &&
    got.every(([b, e], k) => b === truth[k][0] && e.c.length === 0 && e.b === truth[k][1]);
  if (!match) {
    fail = {
      i, why: 'value-mismatch',
      got: got.slice(-8).map(([b, e]) => `${b.toString(2).padStart(4, '0')}^${e.b}`).join(' '),
      want: truth.slice(-8).map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${c}`).join(' '),
    };
    break;
  }
  ok++;
  if (ok % 25000 === 0) console.log(`  ${ok} transitions composed exactly`);
}
if (fail) {
  console.log(`FAIL at transition ${fail.i}: ${fail.why}`);
  if (fail.got) { console.log(`  got : … ${fail.got}`); console.log(`  want: … ${fail.want}`); }
  const L = anchors[fail.i];
  console.log(`  pre : … ${L.slice(-8).map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${c}`).join(' ')}`);
  process.exit(1);
}
console.log(`\nALL PASS: ${ok} consecutive transitions reproduced by pure lemma composition (no tape simulation)`);
