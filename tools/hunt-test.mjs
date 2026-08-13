import { parseMachine } from '../src/machine.mjs';
import { runNaive } from '../src/naive.mjs';
import { huntMachine } from '../src/hunt.mjs';

// Pipeline self-test on 3-state machines: enumerate a slice of the space,
// keep machines that neither halt quickly nor die to the concrete certs, and
// require that the symbolic-rule path proves several of them non-halting.
// Every claimed proof is cross-checked by naive simulation (no halt to 1e7).
const SYMS = [];
for (const w of [0, 1]) for (const d of ['L', 'R']) for (const s of ['A', 'B', 'C']) SYMS.push(`${w}${d}${s}`);

let tried = 0, ruleProofs = 0, otherProofs = 0, crossFail = 0;
outer:
for (let i1 = 0; i1 < 12; i1++) for (let i2 = 0; i2 < 12; i2 += 2) for (let i3 = 0; i3 < 12; i3 += 3) for (let i4 = 0; i4 < 12; i4 += 2) {
  const code = `1RB${SYMS[i1]}_${SYMS[i2]}${SYMS[i3]}_${SYMS[i4]}1RZ`;
  const m = parseMachine(code);
  const quick = runNaive(m, 5000);
  if (quick.halted) continue;
  tried++;
  const r = huntMachine(m, [1, 2], { maxOps: 3000 });
  if (r.verdict === 'nonhalt') {
    const check = runNaive(m, 1e7);
    if (check.halted) { crossFail++; console.log(`CROSS-CHECK FAIL: ${code} claimed ${r.cert.type} but halts at ${check.steps}`); }
    else if (r.cert.type === 'inductive-rule') {
      if (ruleProofs < 5) console.log(`rule proof: ${code}\n  ${r.cert.config}\n  A=${JSON.stringify(r.cert.A)} d=${JSON.stringify(r.cert.d)} n0=${r.cert.n0} n1=${r.cert.n1}`);
      ruleProofs++;
    } else otherProofs++;
  }
  if (ruleProofs >= 40) break outer;
}
console.log(`\ntried=${tried} ruleProofs=${ruleProofs} otherProofs=${otherProofs} crossFail=${crossFail}`);
process.exit(crossFail === 0 && ruleProofs > 0 ? 0 : 1);
