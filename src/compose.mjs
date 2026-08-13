// Milestone 2 composition calculus: apply proven one-sweep lemmas to
// symbolic configurations by affine algebra alone — no tape simulation.
// A lemma here is {blocks, counts (BigInt, param positions overridden),
// params (positions), post ([[block, expr-over-lemma-params]]), steps,
// n0, withContext}. A config is {runs: [[block, expr-over-global-params]],
// steps: expr, n0: [BigInt]} — runs end at the right edge (anchor side).
//
// Soundness of applying a context-abstracted lemma inside a host config:
// a proven lemma never popped past its window's top run (that would have
// aborted context-touched), so splitting a larger host run into (context
// excess + window top) is a tape no-op. The top window run may therefore
// match a host run with a LARGER count when the lemma's top count is
// concrete; the excess stays behind as context. Formal-param top runs bind
// the whole host run instead (the lemma covers all values ≥ its bound).

const E = (c, b) => ({ c: [...c], b });
export const konstE = (dim, b) => E(new Array(dim).fill(0n), b);
const addE = (e, f) => E(e.c.map((v, i) => v + f.c[i]), e.b + f.b);
const scaleE = (e, s) => E(e.c.map((v) => v * s), e.b * s);
const isConstE = (e) => e.c.every((v) => v === 0n);
const eqE = (e, f) => e.b === f.b && e.c.length === f.c.length && e.c.every((v, i) => v === f.c[i]);
const evalE = (e, n) => e.c.reduce((a, v, i) => a + v * n[i], e.b);

// substitute lemma-space expr (over lemma params) with bindings: an array
// of global-space exprs, one per lemma param. Result is global-space.
const subst = (lemmaExpr, bindings, gDim) => {
  let acc = konstE(gDim, lemmaExpr.b);
  lemmaExpr.c.forEach((coef, j) => { if (coef !== 0n) acc = addE(acc, scaleE(bindings[j], coef)); });
  return acc;
};

// Raise the global lower-bound vector until expr >= min holds at n0.
// Coefficients are nonnegative by construction, so eval at n0 is the
// minimum over the admissible region. Returns false if impossible.
const requireGe = (e, min, n0) => {
  const v = evalE(e, n0);
  if (v >= min) return true;
  const j = e.c.findIndex((c) => c > 0n);
  if (j < 0) return false;
  n0[j] += (min - v + e.c[j] - 1n) / e.c[j];
  return true;
};

export function applyLemma(config, lemma) {
  const gDim = config.n0.length;
  const L = lemma.blocks.length;
  const runs = config.runs;
  if (lemma.withContext && runs.length <= L) return { result: 'too-short' };
  if (!lemma.withContext && runs.length !== L) return { result: 'shape-mismatch' };
  const base = runs.length - L;
  const n0 = [...config.n0];

  // match window (top run last): bind params, check constants
  const bindings = new Array(lemma.params.length);
  let topRemainder = null;
  for (let i = 0; i < L; i++) {
    const [hb, hc] = runs[base + i];
    if (hb !== lemma.blocks[i]) return { result: 'shape-mismatch' };
    const pj = lemma.params.indexOf(i);
    if (pj >= 0) {
      bindings[pj] = hc;
    } else {
      const want = lemma.counts[i];
      if (i === 0 && lemma.withContext) {
        const rem = addE(hc, konstE(gDim, -want));
        if (isConstE(rem) && rem.b === 0n) topRemainder = null;
        else if (isConstE(rem) && rem.b < 0n) return { result: 'count-mismatch' };
        else {
          if (!requireGe(rem, 1n, n0)) return { result: 'count-mismatch' };
          topRemainder = rem;
        }
      } else {
        if (!(isConstE(hc) && hc.b === want)) return { result: 'count-mismatch', runIdx: base + i, want };
      }
    }
  }
  for (let j = 0; j < bindings.length; j++) {
    if (!requireGe(bindings[j], lemma.n0[j], n0)) return { result: 'side-condition' };
  }

  // build post: host prefix + (top remainder) + lemma post (CTX stripped)
  const out = runs.slice(0, base).map(([b, c]) => [b, c]);
  if (topRemainder) out.push([lemma.blocks[0], topRemainder]);
  const postRuns = lemma.post.slice(lemma.withContext ? 1 : 0);
  for (const [b, e] of postRuns) {
    const ge = subst(e, bindings, gDim);
    if (isConstE(ge)) {
      if (ge.b === 0n) continue;
      if (ge.b < 0n) return { result: 'negative-count' };
    } else if (!requireGe(ge, 1n, n0)) return { result: 'negative-count' };
    const top = out[out.length - 1];
    if (top && top[0] === b) top[1] = addE(top[1], ge);
    else out.push([b, ge]);
  }
  return {
    result: 'ok',
    config: { runs: out, steps: addE(config.steps, subst(lemma.steps, bindings, gDim)), n0 },
  };
}

// Apply the first matching lemma from an ordered book. Returns the applied
// lemma's index for grammar extraction.
export function applyBook(config, book) {
  for (let i = 0; i < book.length; i++) {
    const r = applyLemma(config, book[i]);
    if (r.result === 'ok') return { ...r, lemma: i };
  }
  return { result: 'no-lemma' };
}

export const configStr = (cfg) =>
  cfg.runs.map(([b, e]) => `${b.toString(2).padStart(4, '0')}^${exprS(e)}`).join(' ');
const exprS = (e) => {
  const t = e.c.map((v, i) => (v === 0n ? null : `${v === 1n ? '' : v}g${i}`)).filter(Boolean);
  if (e.b !== 0n || t.length === 0) t.push(`${e.b}`);
  return t.join('+').replace(/\+-/g, '-');
};
