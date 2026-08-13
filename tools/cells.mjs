import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';

// Cell-allocation census: at every anchor, count the zone's digit cells
// (blocks strictly between the reservoir run and the tail separator).
// Log every ν where the count changes, with the factored ν and the
// reservoir run before/after — the change points ARE the allocation rule.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const m = parseMachine(CODE);
const macro = makeMacro(m, 4);
const SYM = { 10: 'O', 14: 'e', 11: 'a', 15: 'f' };

const anchors = [];
runMacro(m, 4, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== 2 || s.facing !== 'R' || s.right.length !== 0) return;
    anchors.push(s.left.map(([b, c]) => [b, c]));
  },
});

const factored = (x) => { let k = 0n, o = x; while (o % 2n === 0n && o > 0n) { o /= 2n; k++; } return `${o}·2^${k}`; };

let prev = null;
const events = [];
for (const L of anchors) {
  if (L.length < 6) continue;
  const nu = L[L.length - 2][1] + 2n;
  if (nu < 34n) continue;
  let len = 0n, res = '?';
  for (let i = L.length - 4; i >= 0; i--) {
    const [b, c] = L[i];
    if (SYM[b] === undefined || c >= 60n) { res = `${b.toString(2)}^${c}`; break; }
    len += c;
  }
  if (prev && (len !== prev.len || res !== prev.res)) {
    events.push({ nu, from: prev, to: { len, res } });
  }
  prev = { nu, len, res };
}
console.log(`${events.length} change events`);
for (const e of events.slice(0, 80)) {
  console.log(`ν=${String(e.nu).padStart(7)} = ${factored(e.nu).padEnd(9)} cells ${e.from.len}→${e.to.len}  res ${e.from.res} → ${e.to.res}`);
}
// histogram by odd part of ν
const hist = new Map();
for (const e of events) {
  const odd = (() => { let o = e.nu; while (o % 2n === 0n) o /= 2n; return o; })();
  const key = odd <= 9n ? `odd=${odd}` : 'odd>9';
  hist.set(key, (hist.get(key) ?? 0) + 1);
}
console.log('\nchange events by odd part of ν:', JSON.stringify([...hist.entries()].sort()));
