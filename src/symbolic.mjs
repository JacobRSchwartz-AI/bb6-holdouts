import { HALT } from './machine.mjs';
import { shapeSignature } from './macro.mjs';

// Affine expressions a·n + b (BigInt) over one induction parameter n.
export const X = (a, b) => ({ a, b });
export const C = (b) => X(0n, b);
const add = (e, f) => X(e.a + f.a, e.b + f.b);
const sub1 = (e) => X(e.a, e.b - 1n);
const mul = (e, s) => X(e.a * s, e.b * s);
export const exprStr = (e) =>
  e.a === 0n ? `${e.b}` : `${e.a === 1n ? '' : e.a}n${e.b === 0n ? '' : (e.b > 0n ? '+' : '') + e.b}`;

// Re-run one period of the macro simulation with run paramIdx's count replaced
// by the formal variable n. Success = the machine returns to the same shape at
// an edge event with every other count restored and the parameter now p·n+q,
// under only lower-bound side conditions n ≥ n0. That constitutes a proof of
// the rule C(n) → C(p·n+q) for all n ≥ n0.
export function symbolicPeriod(m, k, macro, snap, paramIdx, opsCap = 200000) {
  const left = [];
  const right = [];
  let i = 0;
  for (const [b, c] of snap.left) left.push([b, i++ === paramIdx ? X(1n, 0n) : C(c)]);
  for (const [b, c] of snap.right) right.push([b, i++ === paramIdx ? X(1n, 0n) : C(c)]);
  let facing = snap.facing;
  let q = snap.q;
  let steps = C(0n);
  let n0 = 1n;

  const requireGe = (e, min) => {
    if (e.a === 0n) return e.b >= min;
    const need = min - e.b;
    if (need > 0n) {
      const bound = (need + e.a - 1n) / e.a;
      if (bound > n0) n0 = bound;
    }
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
      let rule = null;
      for (let j = 0; j < counts.length; j++) {
        const e = counts[j];
        if (j === paramIdx) {
          rule = { p: e.a, q: e.b };
        } else if (e.a !== 0n || e.b !== (j < snap.left.length ? snap.left[j][1] : snap.right[j - snap.left.length][1])) {
          return { result: 'multiparam', ops };
        }
      }
      if (!rule) return { result: 'param-vanished', ops };
      return { result: 'rule', p: rule.p, q: rule.q, steps, n0, ops };
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
        if (rem.a === 0n ? rem.b > 0n : requireGe(rem, 1n)) front.push([block, rem]);
      }
      if (passThrough) push(back, t.block, X(0n, 1n));
      else { push(front, t.block, X(0n, 1n)); facing = facing === 'R' ? 'L' : 'R'; }
      steps = add(steps, X(0n, stepsPer));
      q = t.q;
    }
  }
  return { result: 'no-period', ops: opsCap };
}

// A proved rule C(n) → C(p·n+q) sustains itself iff the parameter never
// shrinks below its starting point: growth from n1 must be non-negative and
// stay ≥ n0. p=1,q=0 is an exact cycle; p=1,q>0 a translated counter; p≥2
// exponential growth.
export function ruleProvesNonhalt(rule, n1) {
  if (n1 < rule.n0) return false;
  if (rule.p === 1n) return rule.q >= 0n;
  if (rule.p >= 2n) return (rule.p - 1n) * n1 + rule.q >= 0n;
  return false;
}
