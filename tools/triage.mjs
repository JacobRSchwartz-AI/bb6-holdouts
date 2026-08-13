import { readFileSync, writeFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro } from '../src/macro.mjs';

const machines = readFileSync('data/open.txt', 'utf8').trim().split('\n');
const OPS = 100000;
const KS = [1, 2, 3, 4];

const rows = [];
const t0 = performance.now();
for (const code of machines) {
  const m = parseMachine(code);
  let best = null;
  for (const k of KS) {
    const r = runMacro(m, k, { maxOps: OPS });
    if (r.status === 'nonhalt' || r.status === 'halt') { best = { k, r }; break; }
    if (!best || r.steps > best.r.steps) best = { k, r };
  }
  rows.push({ code, k: best.k, status: best.r.status, steps: best.r.steps, ops: best.r.ops });
}
const dt = ((performance.now() - t0) / 1000).toFixed(0);

rows.sort((a, b) => (a.steps < b.steps ? 1 : a.steps > b.steps ? -1 : 0));
writeFileSync('data/triage.tsv',
  'machine\tbestK\tstatus\tsteps\tops\n' +
  rows.map((r) => `${r.code}\t${r.k}\t${r.status}\t${r.steps}\t${r.ops}`).join('\n') + '\n');

const certs = rows.filter((r) => r.status === 'nonhalt' || r.status === 'halt');
console.log(`${rows.length} machines triaged in ${dt}s; ${certs.length} decided outright`);
for (const c of certs) console.log(`  ${c.status}: ${c.code}`);
console.log('\ntop compression (steps reached in ' + OPS + ' ops):');
for (const r of rows.slice(0, 15)) console.log(`  ${r.steps}  k=${r.k}  ${r.code}`);
console.log('\nworst compression:');
for (const r of rows.slice(-5)) console.log(`  ${r.steps}  k=${r.k}  ${r.code}`);
