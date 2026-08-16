// N_halt recomputed from the COQ cost model (coq/OdometerCost.v,
// OdometerSpan.v, OdometerSpanSum.v, OdometerDeathCost.v), independently
// of tools/nhalt.mjs. nhalt.mjs uses signed deltas against a baseline;
// this uses the absolute per-transition costs that were measured inside
// the kernel. If the two agree to the digit, the Coq model is right.
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const repo = dirname(dirname(fileURLToPath(import.meta.url)));

// measured in the kernel, one per (wstate, glyph); see coq/OdometerCost.v
const ICOST = {
  F: { O: 3n, e: 4n, a: 3n, f: 4n },
  A: { O: 8n, e: 7n, a: 11n, f: 4n },
  C: { O: 7n, e: 4n, a: 4n, f: 4n },
  D: { O: 3n, e: 3n, a: 3n },
};
const INSTEP = {
  F: { e: ['e', 'F'], f: ['f', 'A'], O: ['e', 'E'], a: ['f', 'E'] },
  A: { O: ['f', 'C'], f: ['f', 'C'], e: ['a', 'E'], a: ['a', 'E'] },
  C: { a: ['a', 'C'], f: ['f', 'F'], O: ['f', 'E'], e: ['f', 'D'] },
  D: { O: ['e', 'Cr'], a: ['f', 'Cr'], e: ['O', 'Cr'] },
};
const INWARD = new Set(['F', 'A', 'C', 'D']);

// mirror of dip_go_cost
function dipCost(W) {
  let s = 'F', deep = [...W], shallow = [], acc = 0n;
  let fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') return acc + 4n * BigInt(shallow.length);
    if (s === 'Cr') {
      if (shallow[0] !== 'f') return null;
      acc += 1n; s = 'F'; continue;
    }
    if (!deep.length) return null;
    const g = deep[0], tr = INSTEP[s]?.[g];
    if (!tr) return null;
    acc += ICOST[s][g];
    const [g2, s2] = tr;
    if (s2 === 'E') { deep = [g2, ...deep.slice(1)]; s = 'E'; continue; }
    if (s2 === 'Cr') { deep = [g2, ...deep.slice(1)]; s = 'Cr'; continue; }
    if (INWARD.has(s2)) { shallow = [g2, ...shallow]; deep = deep.slice(1); s = s2; }
    else { deep = [g2, ...deep.slice(1)]; s = s2; }
  }
  return null;
}

// mirror of dip_go_dies_cost
function diesCost(W) {
  let s = 'F', deep = [...W], shallow = [], acc = 0n;
  let fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') return null;
    if (s === 'Cr') {
      if (shallow[0] !== 'f') return null;
      acc += 1n; s = 'F'; continue;
    }
    if (!deep.length) return s === 'C' ? acc + 1n : null;
    const g = deep[0], tr = INSTEP[s]?.[g];
    if (!tr) return null;
    const [g2, s2] = tr;
    if (s2 === 'E') return null;
    acc += ICOST[s][g];
    if (s2 === 'Cr') { deep = [g2, ...deep.slice(1)]; s = 'Cr'; continue; }
    shallow = [g2, ...shallow]; deep = deep.slice(1); s = s2;
  }
  return null;
}

// fbyte / zwcost / spanBelow, mirroring coq/OdometerSpan.v + SpanSum.v
const FBYTE = [7n, 11n, 7n, 19n, 7n, 11n, 7n, 23n, 7n, 11n, 7n, 19n, 7n, 11n, 7n];
const FPRE = [0n, 7n, 18n, 25n, 44n, 51n, 62n, 69n, 92n, 99n, 110n, 117n, 136n, 143n, 154n, 161n];
const DIGIT = 185n;

function spanBelow(G, v) {
  let acc = 0n;
  for (let g = G; g > 0; g--) {
    const w = v / 16n, d = v % 16n;
    acc += w * DIGIT + FPRE[Number(d)];
    v = w;
  }
  return acc;
}
const tri = (n) => (n * (n - 1n)) / 2n;
const spancost = (G, v, n, m) =>
  16n * (n * m + tri(n) + n) + 45n * n + (spanBelow(G, v + n) - spanBelow(G, v));

// ledger legs, same parse as genledger.mjs
const GCELLS = ['OOO', 'fOO', 'OeO', 'feO', 'Oae', 'fae', 'Ofe', 'ffe',
  'OOa', 'fOa', 'Oea', 'fea', 'Oaf', 'faf', 'Off', 'fff'];
const CV = new Map(GCELLS.map((s, i) => [s, i]));
function parseSpell(W) {
  let G = 0, v = 0n;
  while (2 + 3 * (G + 1) <= W.length) {
    const b = CV.get(W.slice(2 + 3 * G, 2 + 3 * G + 3));
    if (b === undefined) break;
    v += BigInt(b) << BigInt(4 * G); G++;
  }
  return { G, v, T: W.slice(2 + 3 * G) };
}
const spellW = (G, v, T) => {
  let s = 'fO';
  for (let j = 0; j < G; j++) s += GCELLS[Number((v >> BigInt(4 * j)) & 15n)];
  return s + T;
};

const { dying, events } = JSON.parse(readFileSync(join(repo, 'data', 'ledger-events.json'), 'utf8'));
const basev = readFileSync(join(repo, 'coq', 'OdometerBase.v'), 'utf8');
const W_BASE = basev.match(/Definition W_BASE : list glyph := \[([^\]]+)\]/)[1]
  .split(';').map((t) => t.trim().replace('g', '')).join('');
const N_BASE = BigInt(basev.match(/Definition N_BASE : nat := (\d+)/)[1]);
const N_TAIL = BigInt(basev.match(/Definition N_TAIL : nat := (\d+)/)[1]);

const starts = [parseSpell(W_BASE)];
for (const e of events) starts.push(parseSpell(e.after));
const fin = starts[events.length];

let total = N_BASE, m = N_TAIL;
for (let k = 0; k < events.length; k++) {
  const { G, v, T } = starts[k];
  const cap = 16n ** BigInt(G);
  const n = cap - 1n - v;
  const kev = dipCost(spellW(G, cap - 1n, T));
  if (kev === null) throw new Error(`leg ${k}: event dip has no cost`);
  total += spancost(G, v, n, m) + (16n * (m + n + 1n) + 25n + kev);
  m += cap - v;
}
// the final span carries to the dying string, then the fatal sweep
{
  const { G, v, T } = fin;
  const cap = 16n ** BigInt(G);
  const n = cap - 1n - v;
  total += spancost(G, v, n, m);
  m += n;
}
const kd = diesCost(dying);
if (kd === null) throw new Error('dying string does not die');
total += 4n * m + 9n + kd;

const s = total.toString();
console.log(`dies_cost(dying) = ${kd}`);
console.log(`final tail m     = ${m}`);
console.log(`N_halt (Coq model) = ${s}`);
console.log(`digits: ${s.length}`);
