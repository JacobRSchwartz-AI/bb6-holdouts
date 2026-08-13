import { readFileSync } from 'node:fs';

// M2 invariant audit over the working book (grades P-2026-08-13-e):
// per lemma, symbolically —
//   (1) the N-run count (second-to-last run, block 1110) grows exactly +1;
//   (2) the total block extent left of the tail separator is conserved
//       (window pre extent == window post extent, both as affine exprs),
// event lemmas exempted and listed with their extent delta.
const raw = JSON.parse(readFileSync('data/book.json', 'utf8'));
const deE = (e) => ({ c: e.c.map(BigInt), b: BigInt(e.b) });
const book = raw.map((l) => ({
  ...l, counts: l.counts.map(BigInt),
  post: l.post.map(([b, e]) => [b, deE(e)]),
  steps: deE(l.steps), n0: l.n0.map(BigInt),
}));

const CONTEXT = -1;
const isTail = (runs) => {
  // tail = [1111^1, 1110^N, 1010^1] at the end
  const L = runs.length;
  return L >= 3 && runs[L - 1][0] === 0b1010 && runs[L - 2][0] === 0b1110 && runs[L - 3][0] === 0b1111;
};

const zero = (dim) => ({ c: new Array(dim).fill(0n), b: 0n });
const add = (e, f) => ({ c: e.c.map((v, i) => v + (f.c[i] ?? 0n)), b: e.b + f.b });
const eq = (e, f) => e.b === f.b && e.c.every((v, i) => v === (f.c[i] ?? 0n)) && f.c.every((v, i) => v === (e.c[i] ?? 0n));
const exprS = (e) => {
  const t = e.c.map((v, i) => (v === 0n ? null : `${v === 1n ? '' : v}n${i}`)).filter(Boolean);
  if (e.b !== 0n || t.length === 0) t.push(`${e.b}`);
  return t.join('+').replace(/\+-/g, '-');
};

let nOk = 0, nBad = 0, extOk = 0, extBad = 0, skipped = 0;
const nBadList = [], extBadList = [];
for (let li = 0; li < book.length; li++) {
  const l = book[li];
  const dim = l.n0.length;
  // pre runs: blocks + counts (params as unit vectors)
  const preRuns = l.blocks.map((b, i) => {
    const j = l.params.indexOf(i);
    const e = zero(dim);
    if (j >= 0) e.c[j] = 1n;
    else e.b = l.counts[i];
    return [b, e];
  });
  const postRuns = l.post
    .filter(([b]) => b !== CONTEXT)
    .map(([b, e]) => [b, { c: e.c.map((v) => v), b: e.b }]);
  if (!isTail(preRuns) || !isTail(postRuns)) { skipped++; continue; }

  // (1) N-run delta
  const preN = preRuns[preRuns.length - 2][1];
  const postN = postRuns[postRuns.length - 2][1];
  const wantN = add(preN, { c: [], b: 1n });
  if (eq(postN, wantN)) nOk++;
  else { nBad++; if (nBadList.length < 12) nBadList.push({ li, key: l.key, used: l.used, d: `${exprS(preN)} -> ${exprS(postN)}` }); }

  // (2) window extent left of the separator (sum of counts, excluding tail 3 runs)
  let preExt = zero(dim), postExt = zero(dim);
  for (let i = 0; i < preRuns.length - 3; i++) preExt = add(preExt, preRuns[i][1]);
  for (let i = 0; i < postRuns.length - 3; i++) postExt = add(postExt, postRuns[i][1]);
  if (eq(preExt, postExt)) extOk++;
  else {
    extBad++;
    const delta = add(postExt, { c: preExt.c.map((v) => -v), b: -preExt.b });
    if (extBadList.length < 20) extBadList.push({ li, key: l.key, used: l.used, delta: exprS(delta) });
  }
}
console.log(`book: ${book.length} lemmas, ${skipped} skipped (birth/non-anchor-tail shapes)`);
console.log(`N-run +1 law: ${nOk} hold, ${nBad} violate`);
for (const b of nBadList) console.log(`  N-viol #${b.li} used=${b.used} ${b.key}: ${b.d}`);
console.log(`extent conservation: ${extOk} hold, ${extBad} deviate (events expected here)`);
for (const b of extBadList) console.log(`  ext Δ=${b.delta} used=${b.used} #${b.li} ${b.key}`);
