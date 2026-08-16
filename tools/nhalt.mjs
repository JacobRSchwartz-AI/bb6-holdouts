// SUPERSEDED by tools/nhalt-coq.mjs, which is 56 larger and is the
// correct value. The weights below give Ff, AO and Cf no weight and fold
// them into the fixed per-sweep 56; in two of the 549 legs, both at
// G = 69, those counts deviate (AO fires twice, not once) and 28 steps
// are lost each time. coq/OdometerDispute.v settles it on the machine.
// Kept for the record: its derivation and toy validation still stand.
// Exact N_halt (P-2026-08-15-s): BigInt summation of the exact clock law
// over the full orbit, using the ledger's span/event alternation.
//   plain sweep at value v: cost = 56 + 16n + 24*c(v) + wterm(term(v))
//     (carry over a full group fires Cf,Ff,Af = 24; the terminating
//      byte's profile is simulated once per b)
//   event sweep: cost = 56 + 16n + w·rc(dip) + 4*bounces
//   fatal: 4n + 4*crossings + 14
// Validated end-to-end on toy6/toy9 (raw halt steps reproduced exactly)
// before the real run. Usage: node tools/nhalt.mjs [toy6|toy9|real]
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const repo = dirname(dirname(fileURLToPath(import.meta.url)));
const instep = {
  F: { e: ['e', 'F'], f: ['f', 'A'], O: ['e', 'E'], a: ['f', 'E'] },
  A: { O: ['f', 'C'], f: ['f', 'C'], e: ['a', 'E'], a: ['a', 'E'] },
  C: { a: ['a', 'C'], f: ['f', 'F'], O: ['f', 'E'], e: ['f', 'D'] },
  D: { O: ['e', 'Cr'], a: ['f', 'Cr'], e: ['O', 'Cr'] },
};
const toggle = { O: 'f', f: 'O', e: 'a', a: 'e' };
const inward = (s) => s === 'F' || s === 'A' || s === 'C' || s === 'D';
const W8 = { bounces: 4n, Aa: 16n, Ae: 12n, Af: 24n, CO: -4n, Ca: 8n, Fe: 8n };

function dipStats(W) {
  let s = 'F', di = 0, shallow = [], bounces = 0;
  const rc = {};
  const deep = [...W];
  let fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') {
      const out = deep.slice(di);
      for (const g of shallow) out.unshift(toggle[g]);
      return { out, bounces, rc };
    }
    if (s === 'Cr') { if (shallow[0] === 'f') { s = 'F'; bounces++; continue; } throw new Error('Cr'); }
    if (di >= deep.length) return { dies: s === 'C', rc, bounces, crossings: shallow.length };
    const g = deep[di], tr = instep[s]?.[g];
    if (!tr) throw new Error(`${s}/${g}`);
    rc[s + g] = (rc[s + g] ?? 0) + 1;
    const [g2, s2] = tr;
    if (inward(s2)) { shallow.unshift(g2); di++; } else { deep[di] = g2; }
    s = s2;
  }
  throw new Error('fuel');
}
const wOf = (st) => Object.entries(st.rc).reduce((a, [k, c]) => a + (W8[k] ?? 0n) * BigInt(c), 0n)
  + (W8.bounces * BigInt(st.bounces ?? 0));

const GCELLS = ['OOO', 'fOO', 'OeO', 'feO', 'Oae', 'fae', 'Ofe', 'ffe',
  'OOa', 'fOa', 'Oea', 'fea', 'Oaf', 'faf', 'Off', 'fff'];
const CELL_VAL = new Map(GCELLS.map((s, i) => [s, i]));

// wterm(b): weighted cost of the in-group termination on byte b < 15,
// entered in state C (simulate on the 3 cells; must exit within them)
const WTERM = [];
for (let b = 0; b < 15; b++) {
  let s = 'C', i = 0, w = 0n;
  const cells = [...GCELLS[b]];
  while (true) {
    const [g2, s2] = instep[s][cells[i]];
    w += W8[s + cells[i]] ?? 0n;
    if (s2 === 'E') break;
    if (!inward(s2)) throw new Error('unexpected non-inward');
    i++; s = s2;
    if (i >= 3) throw new Error(`b=${b} leaks past the group`);
  }
  WTERM.push(w);
}

// S(X, G) = sum_{v=0}^{X-1} [24*c(v) + wterm(term(v))] for v < 16^G
function S(X, G) {
  let acc = 0n;
  for (let j = 0; j < G; j++) {
    const p = 16n ** BigInt(j), p1 = p * 16n;
    for (let b = 0n; b < 15n; b++) {
      const r = b * p + (p - 1n); // exactly j trailing 15s, digit j = b
      if (r >= X) continue;
      const count = (X - r - 1n) / p1 + 1n;
      acc += count * (24n * BigInt(j) + WTERM[Number(b)]);
    }
  }
  return acc;
}

// parse/setSpell on glyph strings
function parseSpell(W) {
  if (W[0] !== 'f' || W[1] !== 'O') throw new Error('bad head');
  let G = 0, v = 0n;
  while (2 + 3 * (G + 1) <= W.length) {
    const b = CELL_VAL.get(W.slice(2 + 3 * G, 2 + 3 * G + 3));
    if (b === undefined) break;
    v += BigInt(b) << BigInt(4 * G);
    G++;
  }
  return { G, v };
}

// full orbit accumulation from a start string at tail-clock nu0
function nhalt(W0, nu0, base) {
  let W = W0, nu = nu0; // nu = tail-clock of the last completed anchor
  let total = BigInt(base);
  const sum16n = (a, b) => { // sum of 16*(nu-2) for nu in [a, b]
    const cnt = b - a + 1n;
    return 16n * ((a + b) * cnt / 2n - 2n * cnt);
  };
  while (true) {
    const p = parseSpell([...W].join('') === W ? W : W); // W is a string
    const cap = 1n << BigInt(4 * p.G);
    const m = cap - 1n - p.v; // plain sweeps in the span
    if (m > 0n) {
      total += 56n * m + sum16n(nu + 1n, nu + m) + (S(cap - 1n, p.G) - S(p.v, p.G));
      nu += m;
      W = 'fO' + 'fff'.repeat(p.G) + W.slice(2 + 3 * p.G);
    }
    const st = dipStats([...W]);
    if (st.dies) {
      const nDying = nu - 2n;
      const fatal = 4n * nDying + 4n * BigInt(st.crossings) + 14n;
      return { total: total + fatal, nuFatal: nu + 1n, crossings: st.crossings };
    }
    total += 56n + 16n * (nu + 1n - 2n) + wOf(st);
    nu += 1n;
    W = 'f' + st.out.slice(1).join('');
  }
}

const mode = process.argv[2] ?? 'real';
if (mode === 'toy6' || mode === 'toy9') {
  const zone = mode === 'toy6' ? 'fOOOOOOaa' : 'fOOOOOOOOOaa';
  const r = nhalt(zone, 10n, 0); // seed: tail n0=8 -> nu0 = 10
  console.log(`${mode}: N_halt = ${r.total} (fatal sweep nu=${r.nuFatal}, dying crossings=${r.crossings})`);
  console.log(`expected: ${mode === 'toy6' ? 154134 : 33925642}`);
} else {
  const basev = readFileSync(join(repo, 'coq', 'OdometerBase.v'), 'utf8');
  const W_BASE = basev.match(/Definition W_BASE : list glyph := \[([^\]]+)\]/)[1]
    .split(';').map((t) => t.trim().replace('g', '')).join('');
  const r = nhalt(W_BASE, 5n, 354540);
  const s = r.total.toString();
  console.log(`N_halt = ${s}`);
  console.log(`digits: ${s.length}; log2 = ${(s.length - 1 + Math.log10(Number('0.' + s.slice(0, 15)) * 10)) / Math.log10(2)}`);
  console.log(`fatal sweep nu = ${r.nuFatal} (expect 3*2^279 = ${3n * 2n ** 279n})`);
  console.log(`dying crossings = ${r.crossings} (expect 216)`);
}
