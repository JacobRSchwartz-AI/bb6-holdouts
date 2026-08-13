import { parseMachine } from '../src/machine.mjs';
import { runMacro } from '../src/macro.mjs';

// Sample anchor-event count vectors in given ops windows, to inspect the
// post-2^16 regime of the Odometer.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const windows = [[985000, 995000], [2000000, 2000400], [10000000, 10000400], [49000000, 49000400]];
const maxOps = Math.max(...windows.map(([, b]) => b));
const hits = new Map(windows.map((w) => [w.join('-'), []]));

runMacro(m, 4, {
  maxOps,
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    for (const w of windows) {
      if (s.ops >= w[0] && s.ops <= w[1]) {
        const list = hits.get(w.join('-'));
        if (list.length < 8) list.push({ ops: s.ops, counts: s.left.map(([, c]) => c) });
      }
    }
  },
});

for (const [w, list] of hits) {
  console.log(`\n=== ops window ${w} (${list.length} shown) ===`);
  for (const h of list) console.log(`  @${h.ops} len=${h.counts.length}: [${h.counts.join(',')}]`);
}
