import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro, shapeSignature, formatConfig } from '../src/macro.mjs';

const args = process.argv.slice(2);
const flags = {};
const positional = [];
for (let i = 0; i < args.length; i++) {
  if (args[i].startsWith('--')) flags[args[i].slice(2)] = args[i + 1], i++;
  else positional.push(args[i]);
}
const m = parseMachine(positional[0]);
const k = Number(flags.k ?? 1);
const maxOps = Number(flags.ops ?? 500000);
const show = Number(flags.show ?? 40);

const edges = [];
const r = runMacro(m, k, {
  maxOps,
  onEdge: (s) => { if (edges.length < 500000) edges.push(s); },
});
console.log(`status=${r.status} steps=${r.steps} ops=${r.ops} edgeEvents=${edges.length}\n`);

const sigIds = new Map();
const sigMeta = [];
for (const s of edges) {
  const sig = shapeSignature(s.left, s.right, s.facing, s.q);
  if (!sigIds.has(sig)) {
    sigIds.set(sig, sigIds.size);
    sigMeta.push({ sig, template: formatConfig(s.left, s.right, s.facing, s.q, k).replace(/\^\d+/g, '^·'), snaps: [] });
  }
  s.id = sigIds.get(sig);
  sigMeta[s.id].snaps.push(s);
}
const counts = (s) => [...s.left.map(([, c]) => c), ...s.right.map(([, c]) => c)];

if (flags.mode === 'timeline') {
  const groups = [];
  for (const s of edges) {
    const last = groups[groups.length - 1];
    if (last && last.id === s.id) { last.n++; last.last = s; }
    else groups.push({ id: s.id, n: 1, first: s, last: s });
  }
  console.log(`${groups.length} timeline groups over ${sigIds.size} distinct shapes; last ${show}:`);
  for (const g of groups.slice(-show)) {
    const c1 = counts(g.first).join(',');
    const c2 = counts(g.last).join(',');
    console.log(`  S${g.id} ×${g.n}  [${c1}]${g.n > 1 ? ` → [${c2}]` : ''}`);
  }
  console.log('\nshape legend:');
  const seen = new Set(groups.slice(-show).map((g) => g.id));
  for (const id of [...seen].sort((a, b) => a - b)) console.log(`  S${id}: ${sigMeta[id].template}`);
} else {
  const top = [...sigMeta.entries()].sort((a, b) => b[1].snaps.length - a[1].snaps.length).slice(0, Number(flags.sigs ?? 3));
  for (const [id, meta] of top) {
    console.log(`S${id} ×${meta.snaps.length}: ${meta.template}`);
    const rows = meta.snaps.slice(-show);
    for (const s of rows) console.log(`  ops=${String(s.ops).padStart(8)}  [${counts(s).join(', ')}]`);
    console.log();
  }
}
