import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// M3.5 step 1: regime 3's heartbeat. Seed the ink crisis at 3·2^279, let
// the tail conversion fire, then record every tape-edge visit and extract
// the steady cycle: regime 3's anchor shape, its per-sweep transformation,
// and its step cost. Pure observation — no expectations enforced.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const NAME = { 10: 'O', 14: 'e', 11: 'a', 15: 'f', 0: '·' };
const GLYPH = [10, 14, 11, 15];
const O = 10n, E = 14n, A = 11n, F = 15n;
const fmt = (rs) => rs.map(([b, c]) => `${NAME[Number(b)] ?? Number(b).toString(2)}^${c}`).join(' ');
const ST = 'ABCDEF';

function cellGlyph(i, nu) {
  if (i === 0) return 10n;
  const r = (i - 1) % 3;
  if (r === 0) {
    const s = i === 1 ? 0n : BigInt(4 * ((i - 4) / 3) + 4);
    return ((nu >> s) & 1n) === 1n ? 15n : 10n;
  }
  const mt = r === 1 ? (i - 2) / 3 : (i - 3) / 3;
  const s = BigInt(4 * mt + r);
  return BigInt(GLYPH[Number((nu >> s) & 3n)]);
}
const nu0 = 3n * (1n << 279n) - 12n;
const LEFT = [[A, 1n], [E, 1n], [F, 2n], [O, 1n]];
const LEN = 210;
const runs = [];
const push = (b, c) => {
  if (c === 0n) return;
  if (runs.length && runs[runs.length - 1][0] === b) runs[runs.length - 1][1] += c;
  else runs.push([b, c]);
};
for (const [b, c] of LEFT) push(b, c);
for (let i = LEN - 1; i >= 0; i--) push(cellGlyph(i, nu0), 1n);
push(F, 1n); push(E, nu0 - 2n); push(O, 1n);

const events = [];
let prevSteps = 0n, prevGiant = null;
const res = runMacro(m, 4, {
  maxOps: 300000, macro,
  init: { left: runs.map(([b, c]) => [Number(b), c]), right: [], facing: 'R', q: 2, steps: 0n },
  onEdge: (s) => {
    if (s.ops === 1) return;
    const all = [...s.left, ...s.right];
    if (!all.length) return;
    const giant = all.reduce((g, r) => (r[1] > g[1] ? r : g), all[0]);
    if (giant[1] < 1n << 60n) return;
    // signature: which side, state, and the runs BETWEEN the giant run and the tape edge the head is at
    const gi = s.left.indexOf(giant);
    let sig, tailRuns;
    if (s.facing === 'R') {
      tailRuns = gi >= 0 ? s.left.slice(gi + 1) : [];
      sig = `R ${ST[s.q]}> | giant(${NAME[giant[0]]}) ${fmt(tailRuns)}`;
    } else {
      tailRuns = s.right.length ? [...s.right].reverse() : [];
      sig = `L <${ST[s.q]} | edge ${fmt(s.left.slice(0, 3))} … giant(${NAME[giant[0]]})`;
    }
    events.push({
      sig,
      dSteps: s.steps - prevSteps,
      dGiant: prevGiant === null ? 0n : giant[1] - prevGiant,
      ops: s.ops,
    });
    prevSteps = s.steps; prevGiant = giant[1];
  },
});

console.log(`edge events captured: ${events.length} in ${res.ops} ops (status ${res.status})\n`);
console.log('first 40 events (conversion + regime-3 onset):');
for (const e of events.slice(0, 40)) {
  console.log(`  ${e.sig.padEnd(66)} dGiant=${e.dGiant}  dSteps=${e.dSteps.toString().length > 12 ? '~1e' + (e.dSteps.toString().length - 1) : e.dSteps}`);
}
console.log('\nsignature census over the steady tail (events 100+):');
const census = new Map();
for (const e of events.slice(100)) {
  const key = e.sig;
  if (!census.has(key)) census.set(key, { n: 0, dg: new Set(), ds: new Set() });
  const c = census.get(key);
  c.n++;
  c.dg.add(e.dGiant.toString());
  if (c.ds.size < 6) c.ds.add(e.dSteps.toString().length > 12 ? '~1e' + (e.dSteps.toString().length - 1) : e.dSteps.toString());
}
for (const [sig, c] of [...census.entries()].sort((a, b) => b[1].n - a[1].n).slice(0, 30)) {
  console.log(`  ×${String(c.n).padStart(5)}  ${sig.padEnd(66)} dGiant∈{${[...c.dg].slice(0, 4).join(',')}}  dSteps∈{${[...c.ds].slice(0, 4).join(',')}}`);
}
