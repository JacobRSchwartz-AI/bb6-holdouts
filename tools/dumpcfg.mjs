import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// Dump full anchor run-lists at chosen ν values (args: ν list, default a
// spread over eras) — calibration data for SPELL(ν).
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };

const want = new Set((process.argv.length > 2
  ? process.argv.slice(2)
  : ['34', '35', '40', '48', '63', '64', '65', '90', '96', '97', '150', '192', '200',
    '255', '256', '257', '300', '320', '321', '350', '384', '400', '500', '512', '520',
    '1000', '1024', '1025', '1500', '1536', '1600', '3000', '3072', '3100', '4096',
    '5120', '5200', '6144', '6200', '8192', '8200']).map(BigInt));

runMacro(m, 4, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    const L = s.left;
    if (L.length < 3) return;
    const nu = L[L.length - 2][1] + 2n;
    if (!want.has(nu)) return;
    want.delete(nu);
    const str = L.map(([b, c]) => `${NAME[b] ?? b.toString(2)}^${c}`).join(' ');
    console.log(`ν=${String(nu).padStart(6)}: ${str}`);
  },
});
