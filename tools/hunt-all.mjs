import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { huntMachine } from '../src/hunt.mjs';

const machines = readFileSync('data/open.txt', 'utf8').trim().split('\n');
mkdirSync('certs', { recursive: true });

const tally = {};
const rows = [];
const proofs = [];
const rulesFound = [];
const t0 = performance.now();
for (const code of machines) {
  const m = parseMachine(code);
  const r = huntMachine(m, [1, 2, 3, 4], { maxOps: 200000 });
  const kinds = [...new Set(r.notes.map((n) => n.kind))].sort().join(',') || 'silent';
  tally[r.verdict] = (tally[r.verdict] ?? 0) + 1;
  rows.push(`${code}\t${r.verdict}\t${kinds}`);
  if (r.verdict === 'nonhalt') {
    proofs.push({ code, cert: r.cert });
    writeFileSync(`certs/${code}.json`, JSON.stringify({ machine: code, cert: r.cert }, null, 2));
  }
  const rules = r.notes.filter((n) => n.kind === 'rule');
  if (rules.length) rulesFound.push({ code, rules });
}
const dt = ((performance.now() - t0) / 1000).toFixed(0);

writeFileSync('data/hunt.tsv', 'machine\tverdict\tdiagnoses\n' + rows.join('\n') + '\n');
console.log(`${machines.length} machines hunted in ${dt}s:`, JSON.stringify(tally));
console.log(`\nPROOFS (${proofs.length}):`);
for (const p of proofs) console.log(`  ${p.code}  [${p.cert.type} k=${p.cert.k}]`);
console.log(`\nmachines with verified rules that don't yet close the proof (${rulesFound.length}):`);
for (const r of rulesFound.slice(0, 10)) {
  console.log(`  ${r.code}`);
  for (const rule of r.rules.slice(0, 2)) console.log(`    k=${rule.k} ${rule.rule} steps/period=${rule.stepsPerPeriod}`);
}

const diag = {};
for (const row of rows) for (const kind of row.split('\t')[2].split(',')) diag[kind] = (diag[kind] ?? 0) + 1;
console.log('\ndiagnosis frequencies:', JSON.stringify(diag));
