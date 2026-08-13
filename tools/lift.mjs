import { writeFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { proveLocal, CONTEXT } from '../src/family.mjs';
import { exprStr } from '../src/symbolic.mjs';

// Milestone 2b: the ∀-form lift. One symbolic lemma per tail SKELETON
// (block sequence at a width), with every count position that varies across
// the census — or exceeds the symbolization threshold — as a free formal
// parameter. proveLocal derives the lower-bound side conditions; census
// members below them fall back to exact concrete-template lemmas (the
// lemmas.mjs layer). The union is finite and j-independent: params cover
// all values ≥ n0, concrete lemmas cover the finitely many below.
// Grades prediction P-2026-08-13-d.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const WIDTHS = [5, 8, 12, 999];
const m = parseMachine(CODE);
const macro = makeMacro(m, K_BLOCK);

const anchors = [];
runMacro(m, K_BLOCK, {
  maxOps: 4e6, macro,
  onEdge: (s) => {
    if (s.q !== STATE_C || s.facing !== 'R' || s.right.length !== 0) return;
    anchors.push(s.left.map(([b, c]) => [b, c]));
  },
});
console.log(`${anchors.length} anchors`);

const BIG = 100n;
const skelKey = (L, w) => {
  const eff = Math.min(w, L.length);
  return `w${w > L.length ? L.length : w}|${w < L.length ? 'ctx' : 'full'}|${L.slice(L.length - eff).map(([b]) => b).join(' ')}`;
};

// Pass 1: per-skeleton census of count values at every position.
const skels = new Map();
for (const L of anchors) {
  for (const w of WIDTHS) {
    const key = skelKey(L, w);
    const eff = Math.min(w, L.length);
    const tail = L.slice(L.length - eff);
    let s = skels.get(key);
    if (!s) { s = { blocks: tail.map(([b]) => b), withContext: w < L.length, vals: tail.map(() => new Set()) }; skels.set(key, s); }
    tail.forEach(([, c], i) => { if (s.vals[i].size <= 64) s.vals[i].add(c); });
    if (w >= L.length) break;
  }
}
console.log(`${skels.size} skeletons across widths`);

const ev = (e, vals) => e.c.reduce((a, v, i) => a + v * vals[i], e.b);

function prove(blocks, counts, params, withContext) {
  const dim = params.length;
  const K0 = (b) => ({ c: new Array(dim).fill(0n), b });
  const U = (j) => ({ c: new Array(dim).fill(0n).map((_, i) => (i === j ? 1n : 0n)), b: 0n });
  const left = withContext ? [[CONTEXT, K0(1n)]] : [];
  blocks.forEach((b, i) => {
    const j = params.indexOf(i);
    left.push([b, j >= 0 ? U(j) : K0(counts[i])]);
  });
  const pre = { left, right: [], q: STATE_C, facing: 'R', steps: K0(0n), n0: new Array(dim).fill(1n) };
  const r = proveLocal(m, K_BLOCK, macro, pre, {
    until: (s) => s.q === STATE_C && s.facing === 'R' && s.right.length === 0,
    maxHops: 64,
    opsCap: 20000,
  });
  if (r.result !== 'proved') return { result: r.result };
  return { result: 'proved', post: r.state.left, steps: r.state.steps, n0: r.state.n0 };
}

// Pass 2 (lazy, memoized): lemma FOREST per skeleton. Prove the generic
// ∀-lemma (varying-or-big positions formal); the engine's side conditions
// (n0) exclude small values where runs would be consumed to zero, so for
// every census value observed BELOW a param's derived bound, re-prove a
// specialized lemma with that value pinned and the rest still formal.
// Finite by construction; covers every observed value at every position.
const lifted = new Map();
let liftAttempts = 0;
function liftForest(s, counts, params, depth, out) {
  if (out.length > 200 || depth > 6) return;
  const sig = counts.map((c, i) => (params.includes(i) ? '*' : c)).join(',');
  if (out.seen?.has(sig)) return;
  (out.seen ??= new Set()).add(sig);
  if (++liftAttempts % 200 === 0) console.log(`  ${liftAttempts} lift attempts...`);
  const p = prove(s.blocks, counts, params, s.withContext);
  if (p.result === 'proved') {
    out.push({ counts: [...counts], params: [...params], proof: p, used: 0 });
    for (let j = 0; j < params.length; j++) {
      const pos = params[j];
      const below = [...s.vals[pos]].filter((v) => v < p.n0[j]);
      for (const v of below) {
        const c2 = [...counts]; c2[pos] = v;
        liftForest(s, c2, params.filter((q) => q !== pos), depth + 1, out);
      }
    }
  } else {
    // A failed node (e.g. context-touched with a count formal that must be
    // small for this branch) still owes coverage: pin each param to its
    // observed small values and retry the rest.
    out.fails = (out.fails ?? 0) + 1;
    for (const pos of params) {
      const smalls = [...s.vals[pos]].filter((v) => v <= 4n);
      for (const v of smalls) {
        const c2 = [...counts]; c2[pos] = v;
        liftForest(s, c2, params.filter((q) => q !== pos), depth + 1, out);
      }
    }
  }
}
function liftedLemma(key) {
  if (lifted.has(key)) return lifted.get(key);
  const s = skels.get(key);
  const params = [];
  const counts = [];
  s.vals.forEach((set, i) => {
    const arr = [...set];
    counts.push(arr[0]);
    if (arr.length > 1 || arr[0] > BIG) params.push(i);
  });
  const forest = [];
  liftForest(s, counts, params, 0, forest);
  const entry = { ...s, forest };
  lifted.set(key, entry);
  return entry;
}

// Pass 3: application. Lifted first; exact concrete template as fallback.
const cls = (c) => (c <= BIG ? String(c) : 'big');
const concrete = new Map();
function concreteLemma(L, w) {
  const eff = Math.min(w, L.length);
  const withContext = w < L.length;
  const tail = L.slice(L.length - eff);
  const key = `w${eff}|${withContext ? 'ctx' : 'full'}|${tail.map(([b, c]) => `${b}:${cls(c)}`).join(' ')}`;
  if (!concrete.has(key)) {
    const params = [];
    tail.forEach(([, c], i) => { if (c > BIG) params.push(i); });
    const p = prove(tail.map(([b]) => b), tail.map(([, c]) => c), params, withContext);
    concrete.set(key, { params, proof: p, used: 0 });
  }
  return concrete.get(key);
}

let explained = 0, viaLift = 0, viaConcrete = 0, unexplained = 0, mismatch = 0;
const unexplainedSamples = [];
for (let i = 0; i < anchors.length - 1; i++) {
  if (i % 50000 === 0 && i > 0) console.log(`  progress ${i}/${anchors.length}: lift=${viaLift} concrete=${viaConcrete} unexplained=${unexplained} MISMATCH=${mismatch}`);
  const L = anchors[i];
  let hit = null;
  for (const w of WIDTHS) {
    const eff = Math.min(w, L.length);
    const tail = L.slice(L.length - eff);
    const lf = liftedLemma(skelKey(L, w));
    for (const lem of lf.forest) {
      if (lem.proof.result !== 'proved') continue;
      const vals = lem.params.map((pi) => tail[pi][1]);
      const constOk = tail.every(([, c], pi) => lem.params.includes(pi) || c === lem.counts[pi]);
      if (constOk && lem.proof.n0.every((b, j) => vals[j] >= b)) { hit = { proof: lem.proof, params: lem.params, vals, ctx: lf.withContext, kind: 'lift' }; lem.used++; break; }
    }
    if (hit) break;
    const cl = concreteLemma(L, w);
    if (cl.proof.result === 'proved') {
      const vals = cl.params.map((pi) => tail[pi][1]);
      if (cl.proof.n0.every((b, j) => vals[j] >= b)) { hit = { proof: cl.proof, params: cl.params, vals, ctx: w < L.length, kind: 'concrete' }; cl.used++; break; }
    }
    if (w >= L.length) break;
  }
  if (!hit) {
    unexplained++;
    if (unexplainedSamples.length < 6) unexplainedSamples.push({ i, N: L.length >= 2 ? L[L.length - 2][1] : 0n, tail: L.slice(-6).map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${c}`).join(' ') });
    continue;
  }
  const predicted = hit.proof.post.slice(hit.ctx ? 1 : 0).map(([b, c]) => [b, ev(c, hit.vals)]);
  const next = anchors[i + 1];
  const actualTail = next.slice(next.length - predicted.length);
  const ok = predicted.length === actualTail.length &&
    predicted.every(([b, c], k) => b === actualTail[k][0] && c === actualTail[k][1]);
  if (ok) { explained++; if (hit.kind === 'lift') viaLift++; else viaConcrete++; }
  else mismatch++;
}

const pairs = anchors.length - 1;
const allForest = [...lifted.values()].flatMap((l) => l.forest);
const liftOk = allForest.filter((l) => l.proof.result === 'proved');
const failNodes = [...lifted.values()].reduce((a, l) => a + (l.forest.fails ?? 0), 0);
console.log(`\nlift attempts: ${liftAttempts}, forest lemmas proved: ${liftOk.length}, failed nodes (specialized past): ${failNodes}`);
const concreteUsed = [...concrete.values()].filter((c) => c.used > 0);
console.log(`\ncoverage: ${explained}/${pairs} (${(explained / pairs * 100).toFixed(3)}%)  via lifted: ${viaLift} (${(viaLift / pairs * 100).toFixed(3)}%)  via concrete fallback: ${viaConcrete}`);
console.log(`unexplained: ${unexplained}, MISMATCHES (must be 0): ${mismatch}`);
console.log(`final book: ${liftOk.filter((l) => l.used > 0).length} lifted ∀-lemmas used + ${concreteUsed.length} concrete small-count lemmas used`);
for (const s of unexplainedSamples) console.log(`  unexplained @N=${s.N}: … ${s.tail}`);

const out = [];
for (const [key, lf] of lifted.entries()) {
  for (const l of lf.forest) {
    if (l.proof.result !== 'proved' || l.used === 0) continue;
    out.push(`LIFTED used=${l.used} ${key}`);
    out.push(`  pre : ${lf.withContext ? 'CTX ' : ''}${lf.blocks.map((b, i) => `${b.toString(2).padStart(4, '0')}^${l.params.includes(i) ? `n${l.params.indexOf(i)}` : l.counts[i]}`).join(' ')}`);
    out.push(`  post: ${l.proof.post.map(([b, c]) => `${b === CONTEXT ? 'CTX' : b.toString(2).padStart(4, '0')}^${exprStr(c)}`).join(' ')}`);
    out.push(`  steps=${exprStr(l.proof.steps)}  side: n >= [${l.proof.n0.join(',')}]`);
  }
}
out.push('');
for (const [key, c] of [...concrete.entries()].sort((a, b) => b[1].used - a[1].used)) {
  if (c.proof.result !== 'proved' || c.used === 0) continue;
  out.push(`CONCRETE used=${c.used} ${key}`);
}
writeFileSync('data/rulebook-lifted.txt', out.join('\n') + '\n');
console.log('wrote data/rulebook-lifted.txt');

// Serialize the full proven book (all forest lemmas + used concrete pins)
// for the composition layer. Order: width ascending, forest order within a
// skeleton (generic before specializations), so first-match application in
// compose replays this run's selection exactly.
const serE = (e) => ({ c: e.c.map(String), b: String(e.b) });
const bookOut = [];
const widthOf = (key) => Number(key.match(/^w(\d+)/)[1]);
const keysSorted = [...lifted.keys()].sort((a, b) => widthOf(a) - widthOf(b));
for (const key of keysSorted) {
  const lf = lifted.get(key);
  for (const l of lf.forest) {
    if (l.proof.result !== 'proved') continue;
    bookOut.push({
      key, kind: 'lift', withContext: lf.withContext, blocks: lf.blocks,
      counts: l.counts.map(String), params: l.params,
      post: l.proof.post.map(([b, c]) => [b, serE(c)]),
      steps: serE(l.proof.steps), n0: l.proof.n0.map(String), used: l.used,
    });
  }
}
const cKeys = [...concrete.keys()].filter((k) => concrete.get(k).proof.result === 'proved' && concrete.get(k).used > 0)
  .sort((a, b) => widthOf(a) - widthOf(b));
for (const key of cKeys) {
  const c = concrete.get(key);
  const withContext = key.includes('|ctx|');
  const tailSpec = key.split('|')[2].split(' ');
  const blocks = tailSpec.map((t) => Number(t.split(':')[0]));
  const counts = tailSpec.map((t, i) => (c.params.includes(i) ? '0' : t.split(':')[1]));
  bookOut.push({
    key, kind: 'concrete', withContext, blocks, counts, params: c.params,
    post: c.proof.post.map(([b, cc]) => [b, serE(cc)]),
    steps: serE(c.proof.steps), n0: c.proof.n0.map(String), used: c.used,
  });
}
bookOut.sort((a, b) => widthOf(a.key) - widthOf(b.key) || (a.kind === b.kind ? 0 : a.kind === 'lift' ? -1 : 1));
writeFileSync('data/book.json', JSON.stringify(bookOut));
console.log(`wrote data/book.json (${bookOut.length} lemmas)`);
