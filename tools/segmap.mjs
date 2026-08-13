import { readFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { applyLemma, konstE } from '../src/compose.mjs';

// M2d step 2: segment-interior map extraction. For depth d, segment A, the
// interior is the 2^d − 1 sweeps at ν ∈ (A·2^d, (A+1)·2^d). Starting from
// the windowed post-carry config with ALL window counts formal, compose the
// (known) lemma sequence symbolically; when a lemma demands a concrete
// count, PIN that parameter (guard) and continue. Result per segment: a
// guarded affine map record. Dedupe records per depth: a finite,
// depth-stable record inventory is the state space of the ∀j induction.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const WIN = 14;   // must exceed the widest lemma window (w12)
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

// attribute: ν -> {lemma, anchorIdx}
import { applyBook } from '../src/compose.mjs';
const START = 5;
const byNu = new Map();
{
  let cfg = { runs: anchors[START].map(([b, c]) => [b, konstE(0, c)]), steps: konstE(0, 0n), n0: [] };
  for (let i = START; i < anchors.length - 1; i++) {
    const r = applyBook(cfg, book);
    if (r.result !== 'ok') break;
    cfg = r.config;
    const L = anchors[i];
    const nu = L.length >= 2 ? L[L.length - 2][1] + 2n : 0n;
    byNu.set(nu, { lemma: r.lemma, idx: i });
  }
}
console.log(`${byNu.size} attributed sweeps`);

const exprKey = (e) => `${e.c.join(',')};${e.b}`;

function extractSegment(d, A) {
  const span = 1n << BigInt(d);
  const startNu = A * span + 1n;
  const first = byNu.get(startNu);
  if (!first) return null;
  const L0 = anchors[first.idx];
  if (L0.length < WIN + 1) return null;   // need real context above the window
  const t = L0.slice(-WIN);
  const dim = WIN;
  const runs = t.map(([b], k) => [b, { c: new Array(dim).fill(0n).map((_, i) => (i === k ? 1n : 0n)), b: 0n }]);
  let cfg = { runs, steps: konstE(dim, 0n), n0: new Array(dim).fill(1n) };
  const guards = new Map();   // paramIdx -> pinned value
  const pinParam = (p, v) => {
    guards.set(p, v);
    const pin = (e) => { e.b += e.c[p] * v; e.c[p] = 0n; };
    for (const [, e] of cfg.runs) pin(e);
    pin(cfg.steps);
  };
  for (let nu = startNu; nu < (A + 1n) * span; nu++) {
    const at = byNu.get(nu);
    if (!at) return null;
    const lemma = book[at.lemma];
    for (let tries = 0; tries < dim + 2; tries++) {
      const r = applyLemma(cfg, lemma);
      if (r.result === 'ok') { cfg = r.config; break; }
      if (r.result === 'count-mismatch' && r.runIdx !== undefined) {
        const e = cfg.runs[r.runIdx][1];
        const live = e.c.map((c, i) => [c, i]).filter(([c]) => c !== 0n);
        if (live.length === 1 && live[0][0] === 1n) {
          pinParam(live[0][1], r.want - e.b);
          continue;
        }
      }
      return { irregular: r.result };
    }
    if (cfg.runs.length > WIN + 8) cfg.runs.splice(0, cfg.runs.length - WIN - 8);   // trim drifting context growth
  }
  const inShape = t.map(([b]) => b).join(' ');
  const outTail = cfg.runs.slice(-WIN);
  const outShape = outTail.map(([b]) => b).join(' ');
  const gPos = [...guards.keys()].sort((a, b) => a - b);
  // structural part: shapes, guard positions, all linear coefficients
  const structKey = `${inShape} :: g[${gPos.join(',')}] -> ${outShape} :: ${outTail.map(([, e]) => e.c.join(',')).join('|')} :: ${cfg.steps.c.join(',')} :: n0 ${cfg.n0.join(',')}`;
  // drifting part: guard values, output offsets, steps offset
  const data = [...gPos.map((p) => guards.get(p)), ...outTail.map(([, e]) => e.b), cfg.steps.b];
  return { structKey, data };
}

const nus = [...byNu.keys()].sort((a, b) => (a < b ? -1 : 1));
const nuMax = nus[nus.length - 1];
for (let d = 4; d <= 12; d++) {
  const span = 1n << BigInt(d);
  const classes = new Map();   // structKey -> {As: [], datas: []}
  let segs = 0, irregular = 0, skipped = 0;
  for (let A = 1n; (A + 1n) * span <= nuMax; A++) {
    const rec = extractSegment(d, A);
    if (!rec) { skipped++; continue; }
    if (rec.irregular) { irregular++; continue; }
    segs++;
    if (!classes.has(rec.structKey)) classes.set(rec.structKey, { As: [], datas: [] });
    const c = classes.get(rec.structKey);
    if (c.As.length < 4096) { c.As.push(A); c.datas.push(rec.data); }
  }
  // per class: is the drifting data affine in A?
  let affClasses = 0, nonAff = 0, tiny = 0;
  const nonAffSamples = [];
  for (const [k, c] of classes) {
    if (c.As.length < 3) { tiny++; continue; }
    const nd = c.datas[0].length;
    let allOk = true;
    for (let q = 0; q < nd; q++) {
      const dA1 = c.As[1] - c.As[0], dv1 = c.datas[1][q] - c.datas[0][q];
      for (let t2 = 2; t2 < c.As.length; t2++) {
        const dA2 = c.As[t2] - c.As[0], dv2 = c.datas[t2][q] - c.datas[0][q];
        if (dv1 * dA2 !== dv2 * dA1) { allOk = false; break; }
      }
      if (!allOk) break;
    }
    if (allOk) affClasses++;
    else { nonAff++; if (nonAffSamples.length < 2) nonAffSamples.push({ k: k.slice(0, 90), As: c.As.slice(0, 6), d0: c.datas.slice(0, 6) }); }
  }
  console.log(`depth ${String(d).padStart(2)}: ${String(classes.size).padStart(4)} structural classes over ${segs} segments | affine-in-A: ${affClasses}, non-affine: ${nonAff}, <3 samples: ${tiny} (irregular ${irregular}, skipped ${skipped})`);
  for (const s of nonAffSamples) console.log(`   non-aff: ${s.k}…  As=${s.As.join(',')}`);
}
