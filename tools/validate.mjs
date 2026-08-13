import { parseMachine } from '../src/machine.mjs';
import { runNaive } from '../src/naive.mjs';
import { runMacro } from '../src/macro.mjs';

const KNOWN = [
  ['1RB1LB_1LA1RZ', 6n],
  ['1RB1RZ_1LB0RC_1LC1LA', 21n],
  ['1RB1LB_1LA0LC_1RZ1LD_1RD0RA', 107n],
  ['1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA', 47176870n],
];

let fail = 0;
for (const [code, expected] of KNOWN) {
  const m = parseMachine(code);
  const naive = runNaive(m, Number(expected) + 10);
  const nOk = naive.halted && BigInt(naive.steps) === expected;
  let line = `${code}  expected=${expected}  naive=${naive.steps}${nOk ? '' : ' ✗'}`;
  for (const k of [1, 2, 3, 4]) {
    const r = runMacro(m, k, { maxOps: 1e8 });
    const ok = r.status === 'halt' && r.steps === expected;
    line += `  k${k}=${r.status === 'halt' ? r.steps : r.status}${ok ? '' : ' ✗'}`;
    if (!ok) fail++;
  }
  if (!nOk) fail++;
  console.log(line);
}
console.log(fail === 0 ? '\nALL PASS' : `\n${fail} FAILURES`);
process.exit(fail === 0 ? 0 : 1);
