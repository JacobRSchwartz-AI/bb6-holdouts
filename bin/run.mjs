import { parseMachine } from '../src/machine.mjs';
import { runNaive } from '../src/naive.mjs';
import { runMacro, formatConfig, shapeSignature, shapeCounts } from '../src/macro.mjs';

const args = process.argv.slice(2);
const flags = {};
const positional = [];
for (let i = 0; i < args.length; i++) {
  if (args[i].startsWith('--')) flags[args[i].slice(2)] = args[i + 1], i++;
  else positional.push(args[i]);
}

const code = positional[0];
if (!code) {
  console.error('usage: node bin/run.mjs <machine> [--k N] [--ops N] [--naive maxSteps] [--sample N]');
  process.exit(1);
}
const m = parseMachine(code);

if (flags.naive) {
  const t0 = performance.now();
  const r = runNaive(m, Number(flags.naive));
  const dt = ((performance.now() - t0) / 1000).toFixed(2);
  console.log(`naive: ${r.halted ? 'HALT' : 'running'} steps=${r.steps} (${dt}s)`);
}

const k = Number(flags.k ?? 1);
const maxOps = Number(flags.ops ?? 1e7);
const samples = [];
const sampleEvery = flags.sample ? Number(flags.sample) : 0;

const t0 = performance.now();
const r = runMacro(m, k, {
  maxOps,
  onSample: sampleEvery
    ? (s) => samples.push({
        ops: s.ops, steps: s.steps,
        sig: shapeSignature(s.left, s.right, s.facing, s.q),
        counts: shapeCounts(s.left, s.right),
        config: formatConfig(s.left, s.right, s.facing, s.q, s.k),
      })
    : null,
  sampleEvery,
});
const dt = ((performance.now() - t0) / 1000).toFixed(2);

console.log(`macro k=${k}: ${r.status}${r.cert ? ' (' + r.cert + ')' : ''} steps=${r.steps} ops=${r.ops} (${dt}s)`);
console.log(`config: ${r.config}`);

if (samples.length) {
  const bySig = new Map();
  for (const s of samples) {
    if (!bySig.has(s.sig)) bySig.set(s.sig, []);
    bySig.get(s.sig).push(s);
  }
  const recurring = [...bySig.entries()].filter(([, v]) => v.length >= 3);
  recurring.sort((a, b) => b[1].length - a[1].length);
  console.log(`\n${samples.length} samples, ${bySig.size} distinct shapes, ${recurring.length} recurring:`);
  for (const [sig, group] of recurring.slice(0, 5)) {
    console.log(`\nshape ×${group.length}: ${group[group.length - 1].config}`);
    const n = group[0].counts.length;
    for (let col = 0; col < n; col++) {
      const vals = group.map((g) => g.counts[col]);
      console.log(`  run[${col}]: ${vals.slice(-8).join(' ')}`);
    }
  }
}
