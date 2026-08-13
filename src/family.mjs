import { symbolicRun } from './symbolic.mjs';

// Context abstraction: a lemma proven from a config whose left stack bottoms
// out in CONTEXT is valid for EVERY tape content beyond that point, because
// the symbolic run fails if the head ever consumes the marker (tape
// locality). Blocks are small non-negative ints; -1 is reserved.
export const CONTEXT = -1;

export function contextGuard(runFn) {
  return (q, block, side) => {
    if (block === CONTEXT) return { halt: false, loop: false, context: true };
    return runFn(q, block, side);
  };
}

// Prove a local rule: from `pre` (stacks of [block, expr] over formal params,
// left stack may bottom out in [CONTEXT, anything]) run symbolically until
// `until(state)` holds. Returns the reached state or a failure diagnosis;
// 'context-touched' means the head left the abstracted window.
export function proveLocal(m, k, macro, pre, { until, opsCap = 100000, onHop = null, maxHops = 10000 }) {
  const guarded = contextGuard(macro);
  const hasCtx = pre.left.some(([b]) => b === CONTEXT);
  let state = { ...pre };
  for (let hops = 0; hops < maxHops; hops++) {
    const r = symbolicRun(m, k, guarded, state, {
      stop: (q, facing) => true,   // stop at every front-empty edge event
      opsCap,
    });
    if (r.result !== 'ok') {
      if (r.result === 'no-stop') return { result: 'no-stop' };
      return r;
    }
    state = { left: r.left, right: r.right, q: r.q, facing: r.facing, steps: r.steps, n0: r.n0 };
    if (hasCtx && state.left.some(([b]) => b === CONTEXT) === false) return { result: 'context-touched' };
    if (onHop) onHop(hops, state);
    if (until(state)) return { result: 'proved', state };
  }
  return { result: 'hop-limit' };
}
