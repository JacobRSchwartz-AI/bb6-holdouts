import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { applyBook, konstE } from '../src/compose.mjs';

// Residue purity: does each lemma fire only at a single ν mod 2^k (for
// some small k)? If so, the book IS a binary-counter case split and
// closure reduces to finite residue coverage. Report per-lemma minimal k
// and the global distribution.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

const raw = JSON.parse(readFileSync('data/book.json', 'utf8'));
const deE = (e) => ({ c: e.c.map(BigInt), b: BigInt(e.b) });
const book = raw.map((l) => ({
  ...l, counts: l.counts.map(BigInt),
  post: l.post.map(([b, e]) => [b, deE(e)]),
  steps: deE(l.steps), n0: l.n0.map(BigInt),
}));

const anchors = [];
runMacro(m, K_BLOCK, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    anchors.push(s.left.map(([b, c]) => [b, c]));
  },
});

const START = 5;
const uses = new Map();   // lemma -> ν list (capped)
{
  let cfg = { runs: anchors[START].map(([b, c]) => [b, konstE(0, c)]), steps: konstE(0, 0n), n0: [] };
  for (let i = START; i < anchors.length - 1; i++) {
    const r = applyBook(cfg, book);
    if (r.result !== 'ok') break;
    cfg = r.config;
    const L = anchors[i];
    const nu = L.length >= 2 ? L[L.length - 2][1] + 2n : 0n;
    if (!uses.has(r.lemma)) uses.set(r.lemma, []);
    const u = uses.get(r.lemma);
    if (u.length < 20000) u.push(nu);
  }
}

const dist = new Map();   // minimal k -> lemma count
let impure = 0;
const impureSamples = [];
for (const [id, nus] of uses) {
  let kMin = -1;
  for (let k = 0; k <= 24; k++) {
    const mod = 1n << BigInt(k);
    const s = new Set(nus.map((v) => (v % mod).toString()));
    if (s.size === 1) { kMin = k; break; }
  }
  if (kMin < 0) {
    impure++;
    if (impureSamples.length < 8) {
      const mod = 1n << 24n;
      const s = new Set(nus.map((v) => (v % mod).toString()));
      impureSamples.push({ id, key: book[id].key, uses: nus.length, residues24: s.size });
    }
  } else {
    dist.set(kMin, (dist.get(kMin) ?? 0) + 1);
  }
}
console.log(`${uses.size} lemmas used; residue-pure: ${uses.size - impure}, impure (no single residue mod 2^24): ${impure}`);
console.log('minimal-k distribution:', JSON.stringify([...dist.entries()].sort((a, b) => a[0] - b[0])));
for (const s of impureSamples) console.log(`  impure #${s.id} used=${s.uses} residues@2^24=${s.residues24}: ${s.key}`);

// purity depth = ρ₂(gcd of pairwise ν differences): all uses agree mod
// 2^depth. Density check: uses ≈ span/2^depth means the lemma fires at
// EVERY ν in its residue class over its active range.
const gcd2 = (x, y) => { x = x < 0n ? -x : x; y = y < 0n ? -y : y; while (y) [x, y] = [y, x % y]; return x; };
const rho2 = (v) => { let r = 0; while (v > 0n && v % 2n === 0n) { v /= 2n; r++; } return r; };
const dd = new Map();
let singles = 0, denseCount = 0, sparseCount = 0;
const sparseSamples = [];
for (const [id, nus] of uses) {
  if (nus.length < 2) { singles++; continue; }
  let g = 0n;
  for (let i = 1; i < nus.length; i++) g = gcd2(g, nus[i] - nus[0]);
  const depth = g === 0n ? 99 : rho2(g);
  dd.set(depth, (dd.get(depth) ?? 0) + 1);
  const span = nus[nus.length - 1] - nus[0];
  const expected = span / (1n << BigInt(Math.min(depth, 60))) + 1n;
  const dense = BigInt(nus.length) * 10n >= expected * 9n;
  if (dense) denseCount++;
  else { sparseCount++; if (sparseSamples.length < 8) sparseSamples.push({ id, used: nus.length, depth, expected: String(expected), key: book[id].key.slice(0, 70) }); }
}
console.log(`purity-depth distribution (multi-use lemmas; ${singles} single-use):`, JSON.stringify([...dd.entries()].sort((a, b) => a[0] - b[0])));
console.log(`dense in residue class over active range: ${denseCount}, sparse: ${sparseCount}`);
for (const s of sparseSamples) console.log(`  sparse #${s.id} used=${s.used} depth=${s.depth} expected≈${s.expected}: ${s.key}`);
