import { runMacro, makeMacro, shapeSignature, formatConfig } from './macro.mjs';
import { symbolicPeriod, ruleProvesNonhalt, exprStr } from './symbolic.mjs';

// Find recurring edge shapes where exactly one run count changes by a
// consistent delta — candidates for a single-parameter inductive rule.
export function detectCandidates(edges) {
  const bySig = new Map();
  for (const s of edges) {
    const sig = shapeSignature(s.left, s.right, s.facing, s.q);
    if (!bySig.has(sig)) bySig.set(sig, []);
    bySig.get(sig).push(s);
  }
  const candidates = [];
  const diagnoses = [];
  for (const [sig, group] of bySig) {
    if (group.length < 3) continue;
    const [s1, s2, s3] = group.slice(-3);
    const c1 = counts(s1), c2 = counts(s2), c3 = counts(s3);
    const changed = [];
    for (let j = 0; j < c1.length; j++) {
      if (c2[j] - c1[j] !== 0n || c3[j] - c2[j] !== 0n) changed.push(j);
    }
    if (changed.length === 1) {
      const j = changed[0];
      candidates.push({ sig, snap: s3, paramIdx: j, n1: c3[j], hits: group.length });
    } else if (changed.length > 1) {
      diagnoses.push({ sig, kind: 'multiparam', params: changed.length, hits: group.length });
    } else {
      diagnoses.push({ sig, kind: 'exact-repeat', hits: group.length });
    }
  }
  candidates.sort((a, b) => b.hits - a.hits);
  return { candidates, diagnoses };
}

const counts = (s) => [...s.left.map(([, c]) => c), ...s.right.map(([, c]) => c)];

export function huntMachine(m, ks = [1, 2, 3, 4], { maxOps = 200000, maxEdges = 500 } = {}) {
  const notes = [];
  for (const k of ks) {
    const macro = makeMacro(m, k);
    const edges = [];
    const r = runMacro(m, k, {
      maxOps, macro,
      onEdge: (s) => { edges.push(s); if (edges.length > maxEdges) edges.shift(); },
    });
    if (r.status === 'nonhalt') return { verdict: 'nonhalt', cert: { type: r.cert, k }, notes };
    if (r.status === 'halt') return { verdict: 'halt', k, steps: r.steps, notes };
    const { candidates, diagnoses } = detectCandidates(edges);
    for (const d of diagnoses) notes.push({ k, ...d });
    for (const cand of candidates.slice(0, 4)) {
      const v = symbolicPeriod(m, k, macro, cand.snap, cand.paramIdx);
      if (v.result === 'rule') {
        const rule = { p: v.p, q: v.q, n0: v.n0 };
        const note = {
          k, kind: 'rule', hits: cand.hits, paramIdx: cand.paramIdx, n1: cand.n1,
          rule: `n -> ${exprStr({ a: v.p, b: v.q })} (n >= ${v.n0})`,
          stepsPerPeriod: exprStr(v.steps),
          config: formatConfig(cand.snap.left, cand.snap.right, cand.snap.facing, cand.snap.q, k),
        };
        notes.push(note);
        if (ruleProvesNonhalt(rule, cand.n1)) {
          return {
            verdict: 'nonhalt',
            cert: {
              type: 'inductive-rule', k,
              config: note.config, paramIdx: cand.paramIdx,
              p: String(v.p), q: String(v.q), n0: String(v.n0), n1: String(cand.n1),
              stepsPerPeriod: exprStr(v.steps),
              reachedAt: { ops: cand.snap.ops, steps: String(cand.snap.steps) },
            },
            notes,
          };
        }
      } else if (v.result === 'proof-runaway' || v.result === 'proof-confined') {
        return { verdict: 'nonhalt', cert: { type: v.result, k }, notes };
      } else {
        notes.push({ k, kind: v.result, hits: cand.hits });
      }
    }
    if (edges.length === 0) notes.push({ k, kind: 'no-edge-visits' });
  }
  return { verdict: 'open', notes };
}
