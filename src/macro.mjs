import { HALT, stateName } from './machine.mjs';

// Accelerated simulation via k-cell macro blocks over an RLE tape.
// Tape = left/right stacks of runs [blockInt, countBigInt], top = nearest head.
// Block bit j (LSB-first) = j-th cell from the block's left edge.
// Two built-in non-halt certificates fall out of the representation:
//  - "confined": head never exits a k-cell window (finite-space loop)
//  - "runaway": head pass-through of a blank block back into the same state,
//    with blank supply infinite (translated cycler into blank tape)

function inBlockSim(m, k, block, side, q0) {
  const { nSymbols, write, move, next } = m;
  const cells = new Uint8Array(k);
  for (let j = 0; j < k; j++) cells[j] = (block >> j) & 1;
  let pos = side === 'L' ? 0 : k - 1;
  let q = q0;
  let steps = 0;
  const bound = m.nStates * k * (1 << k) + 8;
  while (steps < bound) {
    const i = q * nSymbols + cells[pos];
    cells[pos] = write[i];
    pos += move[i];
    q = next[i];
    steps++;
    if (q === HALT) return { halt: true, steps };
    if (pos < 0 || pos >= k) {
      let out = 0;
      for (let j = 0; j < k; j++) out |= cells[j] << j;
      return { block: out, exit: pos < 0 ? 'L' : 'R', q, steps };
    }
  }
  return { loop: true };
}

export function makeMacro(m, k) {
  const memo = new Map();
  return (q, block, side) => {
    const key = ((q * 2 + (side === 'R' ? 1 : 0)) << k) | block;
    let t = memo.get(key);
    if (t === undefined) { t = inBlockSim(m, k, block, side, q); memo.set(key, t); }
    return t;
  };
}

export function runMacro(m, k, { maxOps = 1e7, maxSteps = null, onSample = null, sampleEvery = 0, onEdge = null, macro = null } = {}) {
  macro ??= makeMacro(m, k);

  const left = [];   // [block, count]; count is BigInt
  const right = [];
  let facing = 'R';
  let q = 0;
  let steps = 0n;
  let ops = 0;

  const push = (stack, block, count) => {
    if (stack.length === 0 && block === 0) return;
    const top = stack[stack.length - 1];
    if (top && top[0] === block) top[1] += count;
    else stack.push([block, count]);
  };

  const result = (status, extra = {}) => ({
    status, steps, ops, q, facing,
    config: formatConfig(left, right, facing, q, k),
    ...extra,
  });

  while (ops < maxOps) {
    if (maxSteps !== null && steps >= maxSteps) return result('steps-limit');
    ops++;
    if (sampleEvery && onSample && ops % sampleEvery === 0) {
      onSample({ ops, steps, left, right, facing, q, k });
    }
    const front = facing === 'R' ? right : left;
    if (onEdge && front.length === 0 && left.length + right.length <= 64) {
      onEdge({
        ops, steps, q, facing,
        left: left.map(([b, c]) => [b, c]),
        right: right.map(([b, c]) => [b, c]),
      });
    }
    const back = facing === 'R' ? left : right;
    const enter = facing === 'R' ? 'L' : 'R';
    const run = front.pop() ?? [0, null];        // null count = infinite blank
    const [block, count] = run;
    const t = macro(q, block, enter);
    if (t.halt) return result('halt', { steps: steps + BigInt(t.steps) });
    if (t.loop) return result('nonhalt', { cert: 'confined', block, k });
    const stepsPer = BigInt(t.steps);
    const passThrough = t.exit !== enter;
    if (passThrough && t.q === q) {
      if (count === null) return result('nonhalt', { cert: 'runaway' });
      push(back, t.block, count);
      steps += count * stepsPer;
    } else if (passThrough) {
      push(back, t.block, 1n);
      if (count !== null && count > 1n) front.push([block, count - 1n]);
      steps += stepsPer;
      q = t.q;
    } else {
      if (count !== null && count > 1n) front.push([block, count - 1n]);
      push(front, t.block, 1n);
      steps += stepsPer;
      q = t.q;
      facing = facing === 'R' ? 'L' : 'R';
    }
  }
  return result('ops-limit');
}

const blockStr = (block, k) => {
  let s = '';
  for (let j = 0; j < k; j++) s += (block >> j) & 1;
  return s;
};

export function formatConfig(left, right, facing, q, k, maxRuns = 12) {
  const fmt = ([block, count]) => `${blockStr(block, k)}^${count}`;
  const l = left.slice(-maxRuns).map(fmt);
  if (left.length > maxRuns) l.unshift('…');
  const r = right.slice(-maxRuns).map(fmt).reverse();
  if (right.length > maxRuns) r.push('…');
  const head = facing === 'R' ? `${stateName(q)}>` : `<${stateName(q)}`;
  return ['0^∞', ...l, head, ...r, '0^∞'].join(' ');
}

export function shapeSignature(left, right, facing, q) {
  const l = left.map(([b]) => b).join(',');
  const r = right.map(([b]) => b).join(',');
  return `${l}|${facing}${q}|${r}`;
}

export function shapeCounts(left, right) {
  return [...left.map(([, c]) => c), ...right.map(([, c]) => c)];
}
