import { writeFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro } from '../src/macro.mjs';

// Full-history epoch log for the Odometer. Anchor: head at the right edge of
// written tape, facing right, in state C. Expected count fingerprint
// [1,4,1,1,1, M, <odometer zone>, 1, N, 1]; K = sum of zone.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const maxOps = Number(process.argv[2] ?? 50e6);

const m = parseMachine(CODE);
const rows = [];
const t0 = performance.now();
const r = runMacro(m, K_BLOCK, {
  maxOps,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    rows.push({ ops: s.ops, steps: s.steps, counts: s.left.map(([, c]) => c), blocks: s.left.map(([b]) => b) });
  },
});
const dt = ((performance.now() - t0) / 1000).toFixed(1);
console.log(`sim: ${r.status} ops=${r.ops} steps=${r.steps} (${dt}s); ${rows.length} anchor events`);

const PRE = [1n, 4n, 1n, 1n, 1n];
const parsed = [];
let unparsed = 0, firstUnparsedShown = 0;
for (const row of rows) {
  const c = row.counts;
  const okPre = c.length >= 10 && PRE.every((v, i) => c[i] === v);
  const okSuf = okPre && c[c.length - 3] === 1n && c[c.length - 1] === 1n;
  if (!okSuf) {
    unparsed++;
    if (firstUnparsedShown < 5) { console.log(`  unparsed @ops=${row.ops}: [${c.join(',')}]`); firstUnparsedShown++; }
    continue;
  }
  const M = c[5];
  const zone = c.slice(6, c.length - 3);
  const K = zone.reduce((a, b) => a + b, 0n);
  parsed.push({ ops: row.ops, steps: row.steps, M, K, N: c[c.length - 2], zone });
}
console.log(`parsed ${parsed.length}, unparsed ${unparsed}`);

const epochs = [];
for (const p of parsed) {
  const cur = epochs[epochs.length - 1];
  if (!cur || cur.K !== p.K) epochs.push({ K: p.K, Mset: new Set([String(p.M)]), first: p, last: p, n: 1 });
  else { cur.Mset.add(String(p.M)); cur.last = p; cur.n++; }
}

writeFileSync('data/odometer-edges.tsv',
  'ops\tsteps\tM\tK\tN\tzone\n' +
  parsed.map((p) => `${p.ops}\t${p.steps}\t${p.M}\t${p.K}\t${p.N}\t${p.zone.join(',')}`).join('\n') + '\n');

const lines = ['epoch\tK\tM\tM+K\tN_first\tN_last\tops_first\tops_last\tsteps_last\tvisits'];
epochs.forEach((e, i) => {
  const Ms = [...e.Mset].join('/');
  const mk = e.Mset.size === 1 ? BigInt(Ms) + e.K : 'VARIES';
  lines.push(`${i}\t${e.K}\t${Ms}\t${mk}\t${e.first.N}\t${e.last.N}\t${e.first.ops}\t${e.last.ops}\t${e.last.steps}\t${e.n}`);
});
writeFileSync('data/odometer-epochs.tsv', lines.join('\n') + '\n');
console.log('\n' + lines.join('\n'));

const ratios = [];
for (let i = 1; i < epochs.length; i++) {
  const a = Number(epochs[i - 1].last.N), b = Number(epochs[i].last.N);
  if (a > 0) ratios.push((b / a).toFixed(3));
}
console.log(`\nN_last growth ratios between epochs: ${ratios.join(' ')}`);
