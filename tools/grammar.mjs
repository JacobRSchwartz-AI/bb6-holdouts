import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { applyBook, konstE } from '../src/compose.mjs';

// M2d step 1: infer the generation grammar. Hypothesis: away from event
// sweeps, the lemma applied at counter value ν = N+2 depends only on
// ρ(ν) = trailing zeros of ν (the ruler function) — possibly split by a
// small phase — and NOT on the position within the generation or on j.
// If true, counting segments obey W_{d+1} = W_d · X_d · W_d and the ∀j
// induction is a doubling recurrence over composed affine maps.
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
let cfg = { runs: anchors[START].map(([b, c]) => [b, konstE(0, c)]), steps: konstE(0, 0n), n0: [] };
const seq = [];   // {nu, lemma}
for (let i = START; i < anchors.length - 1; i++) {
  const r = applyBook(cfg, book);
  if (r.result !== 'ok') { console.log(`stopped at ${i}: ${r.result}`); break; }
  cfg = r.config;
  const L = anchors[i];
  const nu = L.length >= 2 ? L[L.length - 2][1] + 2n : 0n;
  seq.push({ nu, lemma: r.lemma });
}
console.log(`${seq.length} transitions attributed`);

const rho = (v) => { let r = 0; while (v % 2n === 0n && v > 0n) { v /= 2n; r++; } return r; };

// Segment-word inventory: for each depth d, cut the attributed sequence
// into aligned segments ν ∈ [A·2^d, (A+1)·2^d) and hash each segment's
// skeleton word. Finite inventory per depth (bounded as d grows) ⇒ a
// finite-state doubling grammar exists; the recurrence is then checked
// as words-of-words.
// Boundary-shape inventory: the doubling induction lives at the MAP level
// (boundary config → boundary config, counts as coordinates). It needs the
// configs at aligned ν = A·2^d to share a small SHAPE inventory (block
// sequence; counts free). Measure that, and for the dominant shape at each
// depth check whether the count-vector drifts AFFINELY with A.
const cfgByNu = new Map();   // ν -> full run list at the anchor BEFORE sweep ν
{
  let c = { runs: anchors[START].map(([b, ct]) => [b, ct]) };
  for (let i = START; i < anchors.length - 1; i++) {
    const L = anchors[i];
    const nu = L.length >= 2 ? L[L.length - 2][1] + 2n : 0n;
    cfgByNu.set(nu, L);
  }
}
const nus = [...cfgByNu.keys()].sort((a, b) => (a < b ? -1 : 1));
const nuMin = nus[0], nuMax = nus[nus.length - 1];
console.log(`\nν range: ${nuMin} .. ${nuMax}`);
// Post-carry windowed boundaries: config at ν = A·2^d + 1 (the depth-≥d
// carry at A·2^d just normalized the low zone), last WIN runs only, deep
// spelling abstracted as context. This is the state space of the interior
// recurrence I_{d+1} = I_d · X_d · I_d.
const WIN = 10;
for (let d = 4; d <= 16; d++) {
  const span = 1n << BigInt(d);
  const shapes = new Map();
  for (let A = (nuMin / span) + 1n; A * span <= nuMax; A++) {
    const L = cfgByNu.get(A * span + 1n);
    if (!L) continue;
    const t = L.slice(-WIN);
    const h = t.map(([b]) => b).join(' ');
    if (!shapes.has(h)) shapes.set(h, { count: 0, As: [], vecs: [] });
    const s = shapes.get(h);
    s.count++;
    if (s.As.length < 512) { s.As.push(A); s.vecs.push(t.map(([, c]) => c)); }
  }
  const inv = [...shapes.entries()].sort((a, b) => b[1].count - a[1].count);
  const total = inv.reduce((a, [, s]) => a + s.count, 0);
  let msg = '';
  for (const [, s] of inv.slice(0, 2)) {
    if (s.As.length >= 3) {
      let affOk = 0;
      const nRuns = s.vecs[0].length;
      for (let k = 0; k < nRuns; k++) {
        let ok = true;
        for (let t2 = 2; t2 < s.As.length; t2++) {
          const dA1 = s.As[1] - s.As[0], dA2 = s.As[t2] - s.As[0];
          const dv1 = s.vecs[1][k] - s.vecs[0][k], dv2 = s.vecs[t2][k] - s.vecs[0][k];
          if (dv1 * dA2 !== dv2 * dA1) { ok = false; break; }
        }
        if (ok) affOk++;
      }
      msg += ` | shape×${s.count}: affine ${affOk}/${nRuns}`;
    } else msg += ` | shape×${s.count}`;
  }
  console.log(`depth ${String(d).padStart(2)}: ${String(shapes.size).padStart(3)} windowed post-carry shapes over ${total}${msg}`);
}

// Map (ρ(ν), ν mod 2^{ρ+?}) — first probe: lemma as function of ρ alone,
// then with a phase bit ν/2^ρ mod 4 (the odd part's low bits).
const byRho = new Map();
for (const { nu, lemma } of seq) {
  if (nu < 8n) continue;
  const r = rho(nu);
  const odd = nu >> BigInt(r);
  const phase = Number(odd & 7n);
  const key = `${r}|${phase}`;
  if (!byRho.has(key)) byRho.set(key, new Map());
  const mm = byRho.get(key);
  const move = book[lemma].key;   // skeleton, not specialization
  mm.set(move, (mm.get(move) ?? 0) + 1);
}

let deterministic = 0, ambiguous = 0;
const ambiguousKeys = [];
for (const [key, mm] of byRho) {
  if (mm.size === 1) deterministic++;
  else { ambiguous++; if (ambiguousKeys.length < 12) ambiguousKeys.push({ key, ids: [...mm.entries()] }); }
}
console.log(`(ρ, odd&7) classes: ${byRho.size}, deterministic: ${deterministic}, ambiguous: ${ambiguous}`);
for (const a of ambiguousKeys) console.log(`  class ${a.key}: lemmas ${a.ids.map(([id, n]) => `#${id}×${n}`).join(', ')}`);

// Which ν are the exceptions? For each ambiguous class, find the minority ν
if (ambiguous > 0) {
  const detail = new Map();
  for (const { nu, lemma } of seq) {
    if (nu < 8n) continue;
    const r = rho(nu);
    const key = `${r}|${Number((nu >> BigInt(r)) & 7n)}`;
    if (!detail.has(key)) detail.set(key, []);
    detail.get(key).push({ nu, move: book[lemma].key });
  }
  for (const a of ambiguousKeys.slice(0, 8)) {
    const rows = detail.get(a.key);
    const majority = a.ids.sort((x, y) => y[1] - x[1])[0][0];
    const excs = rows.filter((r) => r.move !== majority).slice(0, 10);
    console.log(`  class ${a.key} exceptions: ${excs.map((e) => `ν=${e.nu}→${e.move}`).join('  ')}`);
  }
}
