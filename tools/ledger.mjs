// The ledger enumerator (P-2026-08-15-r): fast-forward the abstract dip
// orbit from W_BASE to death as {span-jump | event dip} alternation.
//   span: parse W = f O zgroups(G,v) T with maximal G; jump v -> 16^G - 1
//         (sound by dip_iter_spell for ANY valid decomposition);
//   event: one abstract dip (concrete string -> vm_compute lemma in Coq).
// Cross-check: plain dip iteration must reproduce every event string at
// its sweep index, up to --check N sweeps (default 200000).
// Usage: node tools/ledger.mjs [maxEvents] [checkSweeps]
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const instep = {
  F: { e: ['e', 'F'], f: ['f', 'A'], O: ['e', 'E'], a: ['f', 'E'] },
  A: { O: ['f', 'C'], f: ['f', 'C'], e: ['a', 'E'], a: ['a', 'E'] },
  C: { a: ['a', 'C'], f: ['f', 'F'], O: ['f', 'E'], e: ['f', 'D'] },
  D: { O: ['e', 'Cr'], a: ['f', 'Cr'], e: ['O', 'Cr'] },
};
const toggle = { O: 'f', f: 'O', e: 'a', a: 'e' };
const inward = (s) => s === 'F' || s === 'A' || s === 'C' || s === 'D';

function dip(W) {
  let s = 'F', di = 0, shallow = [];
  const deep = [...W];
  let fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') {
      const out = deep.slice(di);
      for (const g of shallow) out.unshift(toggle[g]);
      return { out };
    }
    if (s === 'Cr') {
      if (shallow[0] === 'f') { s = 'F'; continue; }
      return { fail: 'Cr without f' };
    }
    if (di >= deep.length) return s === 'C' ? { dies: true } : { fail: `falloff ${s}` };
    const g = deep[di], tr = instep[s]?.[g];
    if (!tr) return { fail: `no rule ${s}/${g}` };
    const [g2, s2] = tr;
    if (inward(s2)) { shallow.unshift(g2); di++; }
    else { deep[di] = g2; }
    s = s2;
  }
  return { fail: 'fuel' };
}

// gcells rows (index = 4-bit value), walk order [bit; winlo; winhi]
const GCELLS = [
  'OOO', 'fOO', 'OeO', 'feO', 'Oae', 'fae', 'Ofe', 'ffe',
  'OOa', 'fOa', 'Oea', 'fea', 'Oaf', 'faf', 'Off', 'fff',
];
const CELL_VAL = new Map(GCELLS.map((s, i) => [s, i]));

// maximal-G parse of W = ['f','O', ...groups..., ...T]
function parseSpell(W) {
  if (W[0] !== 'f' || W[1] !== 'O') return null;
  let G = 0, v = 0n;
  while (2 + 3 * (G + 1) <= W.length) {
    const cell = W.slice(2 + 3 * G, 2 + 3 * G + 3).join('');
    const b = CELL_VAL.get(cell);
    if (b === undefined) break;
    v += BigInt(b) << BigInt(4 * G);
    G++;
  }
  return { G, v };
}

function setSpell(W, G, v) {
  const out = [...W];
  for (let g = 0; g < G; g++) {
    const b = Number((v >> BigInt(4 * g)) & 15n);
    const cells = GCELLS[b];
    for (let j = 0; j < 3; j++) out[2 + 3 * g + j] = cells[j];
  }
  return out;
}

// W_BASE from the generated Coq file
const repo = dirname(dirname(fileURLToPath(import.meta.url)));
const basev = readFileSync(join(repo, 'coq', 'OdometerBase.v'), 'utf8');
const wbaseMatch = basev.match(/Definition W_BASE : list glyph := \[([^\]]+)\]/);
const W_BASE = wbaseMatch[1].split(';').map((t) => t.trim().replace('g', ''));
if (W_BASE.length === 0 || W_BASE.some((g) => !'Oeaf'.includes(g))) throw new Error('W_BASE parse');
console.log(`W_BASE: ${W_BASE.length} glyphs`);

const MAX_EVENTS = Number(process.argv[2] ?? 100000);
const CHECK_SWEEPS = Number(process.argv[3] ?? 200000);

// --- fast-forward enumeration ---
let W = [...W_BASE];
let nu = 0n;
const events = []; // { nuBefore, G, v(=cap-1), Wbefore, Wafter|DEATH }
let death = null;
while (events.length < MAX_EVENTS) {
  const p = parseSpell(W);
  if (!p) { console.log('UNPARSEABLE at nu=' + nu, W.join('')); break; }
  const cap = 1n << BigInt(4 * p.G);
  const span = cap - 1n - p.v;
  if (span > 0n) { W = setSpell(W, p.G, cap - 1n); nu += span; }
  const before = W.join('');
  const r = dip(W);
  if (r.dies) { death = { nu: nu + 1n, before }; break; }
  if (r.fail) { console.log(`FAIL at nu=${nu}: ${r.fail}`, before); break; }
  if (r.out[0] !== 'O') { console.log(`BAD SEP at nu=${nu}`, r.out.join('')); break; }
  W = ['f', ...r.out.slice(1)];
  nu += 1n;
  events.push({ nuAfter: nu, G: p.G, before, after: W.join('') });
}

if (death) {
  console.log(`DEATH: fatal sweep is sweep #${death.nu} after the W_BASE anchor`);
  console.log(`       dying string: ${death.before}`);
  console.log(`events (generated lemmas needed): ${events.length}`);
  const nuD = death.nu;
  const theory = 19n * 2n ** 279n;
  console.log(`nu_death - 19*2^279 = ${nuD - theory} (expect small negative offset ~ -nu0)`);
  // crisis entry: last event whose after-string is the crisis form
  const crisis = 'fO' + 'O'.repeat(210) + 'OOaa';
  const ci = events.findIndex((e) => e.after === crisis);
  console.log(ci >= 0
    ? `crisis entry = event #${ci} at nu=${events[ci].nuAfter}; ${events.length - 1 - ci} events after it (expect 7)`
    : 'crisis-entry string NEVER appears as an event output (grade P3 accordingly)');
} else {
  console.log(`NO DEATH within ${events.length} events; nu=${nu}`);
  console.log('last strings:', events.slice(-3).map((e) => e.after));
}

// --- cross-check against plain iteration ---
const byNu = new Map(events.filter((e) => e.nuAfter <= BigInt(CHECK_SWEEPS)).map((e) => [e.nuAfter, e.after]));
let Wp = [...W_BASE];
let ok = true, checked = 0;
for (let i = 1n; i <= BigInt(CHECK_SWEEPS); i++) {
  const r = dip(Wp);
  if (r.dies || r.fail) {
    if (death && i === death.nu) console.log(`plain-check: death reproduced at sweep ${i}`);
    else { console.log(`plain-check DIVERGED at ${i}:`, r); ok = false; }
    break;
  }
  Wp = ['f', ...r.out.slice(1)];
  const want = byNu.get(i);
  if (want !== undefined) {
    checked++;
    if (Wp.join('') !== want) { console.log(`plain-check MISMATCH at sweep ${i}`); ok = false; break; }
  }
}
console.log(`plain-check: ${checked} event strings verified over ${CHECK_SWEEPS} sweeps: ${ok ? 'OK' : 'FAIL'}`);

// dump for genledger + inspection
import { writeFileSync } from 'node:fs';
writeFileSync(join(repo, 'data', 'ledger-events.json'), JSON.stringify({
  nuDeath: death ? death.nu.toString() : null,
  dying: death ? death.before : null,
  events: events.map((e) => ({ nuAfter: e.nuAfter.toString(), G: e.G, before: e.before, after: e.after })),
}, null, 1));
console.log('dumped data/ledger-events.json');
