import { HALT } from './machine.mjs';
import { shapeSignature } from './macro.mjs';

// Affine expressions c·n + b over an m-vector of induction parameters n.
// Coefficients are always ≥ 0 by construction (counts start as unit vectors
// or constants and only ever add), so every side condition reduces to raising
// a componentwise lower bound n0 — no upper bounds can arise.
const E = (c, b) => ({ c, b });
const konst = (mDim, b) => E(new Array(mDim).fill(0n), b);
const unit = (mDim, j) => E(new Array(mDim).fill(0n).map((_, i) => (i === j ? 1n : 0n)), 0n);
const add = (e, f) => E(e.c.map((v, i) => v + f.c[i]), e.b + f.b);
const sub1 = (e) => E(e.c, e.b - 1n);
const mul = (e, s) => E(e.c.map((v) => v * s), e.b * s);
const evalAt = (e, n) => e.c.reduce((acc, v, i) => acc + v * n[i], e.b);
const isConst = (e) => e.c.every((v) => v === 0n);
export const exprStr = (e) => {
  const terms = e.c.map((v, i) => (v === 0n ? null : `${v === 1n ? '' : v}n${i}`)).filter(Boolean);
  if (e.b !== 0n || terms.length === 0) terms.push(`${e.b}`);
  return terms.join('+').replace(/\+-/g, '-');
};

// Verify one period of the macro simulation with the counts at paramIdxs
// replaced by formal variables. Success: the machine returns to the same
// shape at an edge event with non-parameter counts restored and parameter
// counts forming an affine map A·n + d, valid for all n ≥ n0 componentwise.
export function symbolicPeriod(m, k, macro, snap, paramIdxs, opsCap = 200000) {
  const mDim = paramIdxs.length;
  const origCounts = [...snap.left.map(([, c]) => c), ...snap.right.map(([, c]) => c)];
  const left = [];
  const right = [];
  let i = 0;
  for (const [b, c] of snap.left) { const j = paramIdxs.indexOf(i++); left.push([b, j >= 0 ? unit(mDim, j) : konst(mDim, c)]); }
  for (const [b, c] of snap.right) { const j = paramIdxs.indexOf(i++); right.push([b, j >= 0 ? unit(mDim, j) : konst(mDim, c)]); }
  let facing = snap.facing;
  let q = snap.q;
  let steps = konst(mDim, 0n);
  const n0 = new Array(mDim).fill(1n);

  const requireGe = (e, min) => {
    const v = evalAt(e, n0);
    if (v >= min) return true;
    const j = e.c.findIndex((c) => c > 0n);
    if (j < 0) return false;
    n0[j] += (min - v + e.c[j] - 1n) / e.c[j];
    return true;
  };

  const push = (stack, block, count) => {
    if (stack.length === 0 && block === 0) return;
    const top = stack[stack.length - 1];
    if (top && top[0] === block) top[1] = add(top[1], count);
    else stack.push([block, count]);
  };

  const startSig = shapeSignature(snap.left, snap.right, facing, q);

  for (let ops = 0; ops < opsCap; ops++) {
    const front = facing === 'R' ? right : left;
    const back = facing === 'R' ? left : right;
    if (front.length === 0 && ops > 0 && shapeSignature(left, right, facing, q) === startSig) {
      const counts = [...left.map(([, c]) => c), ...right.map(([, c]) => c)];
      const A = [];
      const d = [];
      for (let pos = 0; pos < counts.length; pos++) {
        const e = counts[pos];
        const j = paramIdxs.indexOf(pos);
        if (j >= 0) { A[j] = e.c; d[j] = e.b; }
        else if (!isConst(e) || e.b !== origCounts[pos]) return { result: 'widen', position: pos, ops };
      }
      return { result: 'rule', A, d, steps, n0, ops };
    }
    const enter = facing === 'R' ? 'L' : 'R';
    const run = front.pop() ?? [0, null];
    const [block, count] = run;
    const t = macro(q, block, enter);
    if (t.halt) return { result: 'halt-reached', ops };
    if (t.loop) return { result: 'proof-confined', n0, ops };
    const stepsPer = BigInt(t.steps);
    const passThrough = t.exit !== enter;
    if (passThrough && t.q === q) {
      if (count === null) return { result: 'proof-runaway', n0, ops };
      push(back, t.block, count);
      steps = add(steps, mul(count, stepsPer));
    } else {
      if (count !== null) {
        const rem = sub1(count);
        if (isConst(rem) ? rem.b > 0n : requireGe(rem, 1n)) front.push([block, rem]);
      }
      if (passThrough) push(back, t.block, konst(mDim, 1n));
      else { push(front, t.block, konst(mDim, 1n)); facing = facing === 'R' ? 'L' : 'R'; }
      steps = add(steps, konst(mDim, stepsPer));
      q = t.q;
    }
  }
  return { result: 'no-period', ops: opsCap };
}

// Free-running symbolic execution: advance a symbolic state (expr counts)
// until the head next sits at an empty front matching `stop(q, facing)`.
// Mutates nothing; returns a new state or a failure diagnosis. The state's
// n0 lower-bound vector accumulates across chained calls.
export function symbolicRun(m, k, macro, state, { stop, opsCap = 100000, loopCollapse = false } = {}) {
  const mDim = state.n0.length;
  const left = state.left.map(([b, c]) => [b, c]);
  const right = state.right.map(([b, c]) => [b, c]);
  let { q, facing } = state;
  let steps = state.steps;
  const n0 = [...state.n0];

  // Symbolic loop collapse: when the configuration shape (blocks, coeff
  // vectors, state, facing) recurs with every count offset shifted by a
  // constant and EXACTLY ONE count draining by 1 per cycle, the loop's
  // branch decisions are count-independent for all remaining iterations,
  // so jump t* = drained−1 cycles in one affine update.
  const seen = loopCollapse ? new Map() : null;
  const shapeOf = () => {
    const part = (st) => st.map(([b, c]) => `${b}·${c.c.join(',')}`).join(' ');
    return `${q}|${facing}|${part(left)}#${part(right)}|${steps.c.join(',')}`;
  };
  const dbg = typeof process !== 'undefined' && process.env.DBG_COLLAPSE;
  const tryCollapse = (ops) => {
    const key = shapeOf();
    const prev = seen.get(key);
    const counts = [...left.map(([, c]) => c), ...right.map(([, c]) => c)];
    const snap = { bs: counts.map((c) => c.b), stepB: steps.b };
    if (!prev) { if (seen.size < 20000) seen.set(key, snap); return; }
    const db = snap.bs.map((b, i) => b - prev.bs[i]);
    const negs = db.map((d, i) => [d, i]).filter(([d]) => d < 0n);
    if (dbg) console.log(`  [dbg ${ops}] prev-hit, db=[${db.join(',')}] negs=${negs.length}`);
    if (negs.length !== 1 || negs[0][0] !== -1n || db.length !== prev.bs.length) { seen.set(key, snap); return; }
    const di = negs[0][1];
    const drained = counts[di];
    const tStar = E(drained.c, drained.b - 1n);            // (drained − 1) iterations
    for (let i = 0; i < counts.length; i++) {
      if (db[i] === 0n) continue;
      const s = i < left.length ? left : right;
      const j = i < left.length ? i : i - left.length;
      s[j][1] = add(s[j][1], mul(tStar, db[i]));
    }
    steps = add(steps, mul(tStar, snap.stepB - prev.stepB));
    seen.clear();
  };

  const requireGe = (e, min) => {
    const v = evalAt(e, n0);
    if (v >= min) return true;
    const j = e.c.findIndex((c) => c > 0n);
    if (j < 0) return false;
    n0[j] += (min - v + e.c[j] - 1n) / e.c[j];
    return true;
  };
  const push = (stack, block, count) => {
    if (stack.length === 0 && block === 0) return;
    const top = stack[stack.length - 1];
    if (top && top[0] === block) top[1] = add(top[1], count);
    else stack.push([block, count]);
  };

  for (let ops = 0; ops < opsCap; ops++) {
    const front = facing === 'R' ? right : left;
    const back = facing === 'R' ? left : right;
    if (front.length === 0 && ops > 0 && stop(q, facing)) {
      return { result: 'ok', left, right, q, facing, steps, n0, ops };
    }
    if (seen && ops > 512) {
      tryCollapse(ops);
      if (typeof process !== 'undefined' && process.env.DBG_COLLAPSE && ops % 500 === 0) {
        console.log(`  [dbg ${ops}] seen=${seen.size} q=${q} f=${facing} L=${left.map(([b, c]) => `${b}^${exprStr(c)}`).slice(-4).join(' ')} R=${right.map(([b, c]) => `${b}^${exprStr(c)}`).slice(-4).join(' ')}`);
      }
    }
    const enter = facing === 'R' ? 'L' : 'R';
    const run = front.pop() ?? [0, null];
    const [block, count] = run;
    const t = macro(q, block, enter);
    if (t.context) return { result: 'context-touched', ops };
    if (t.halt) return { result: 'halt-reached', ops };
    if (t.loop) return { result: 'proof-confined', n0, ops };
    const stepsPer = BigInt(t.steps);
    const passThrough = t.exit !== enter;
    if (passThrough && t.q === q) {
      if (count === null) return { result: 'proof-runaway', n0, ops };
      push(back, t.block, count);
      steps = add(steps, mul(count, stepsPer));
    } else {
      if (count !== null) {
        const rem = sub1(count);
        if (isConst(rem) ? rem.b > 0n : requireGe(rem, 1n)) front.push([block, rem]);
      }
      if (passThrough) push(back, t.block, konst(mDim, 1n));
      else { push(front, t.block, konst(mDim, 1n)); facing = facing === 'R' ? 'L' : 'R'; }
      steps = add(steps, konst(mDim, stepsPer));
      q = t.q;
    }
  }
  return { result: 'no-stop', ops: opsCap };
}

export function makeSymbolicState(snap, paramIdxs) {
  const mDim = paramIdxs.length;
  const left = [];
  const right = [];
  let i = 0;
  for (const [b, c] of snap.left) { const j = paramIdxs.indexOf(i++); left.push([b, j >= 0 ? unit(mDim, j) : konst(mDim, c)]); }
  for (const [b, c] of snap.right) { const j = paramIdxs.indexOf(i++); right.push([b, j >= 0 ? unit(mDim, j) : konst(mDim, c)]); }
  return { left, right, q: snap.q, facing: snap.facing, steps: konst(mDim, 0n), n0: new Array(mDim).fill(1n) };
}

export const evalExprAt = evalAt;

// A rule n → A·n + d self-sustains iff n1 ≥ n0 and A·n1 + d ≥ n1
// componentwise: A is nonnegative, so the iteration is monotone and the
// parameter vector never re-enters the region below n0.
export function ruleProvesNonhalt(rule, n1) {
  const { A, d, n0 } = rule;
  const mDim = n0.length;
  for (let j = 0; j < mDim; j++) if (n1[j] < n0[j]) return false;
  for (let j = 0; j < mDim; j++) {
    const next = A[j].reduce((acc, v, i) => acc + v * n1[i], d[j]);
    if (next < n1[j]) return false;
  }
  return true;
}

export const ruleStr = (rule) =>
  rule.A.map((row, j) => `n${j} -> ${exprStr({ c: row, b: rule.d[j] })}`).join('; ') +
  ` (n >= [${rule.n0.join(',')}])`;
