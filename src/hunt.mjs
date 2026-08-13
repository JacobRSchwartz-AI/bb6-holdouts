import { runMacro, makeMacro, shapeSignature, formatConfig } from './macro.mjs';
import { symbolicPeriod, ruleProvesNonhalt, ruleStr, exprStr } from './symbolic.mjs';

// Find recurring edge shapes whose count deltas are consistent between
// consecutive visits — candidates for an inductive rule in 1..MAXP variables.
const MAXP = 6;

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
    if (changed.length >= 1 && changed.length <= MAXP) {
      candidates.push({ sig, snap: s3, paramIdxs: changed, n1: changed.map((j) => c3[j]), hits: group.length });
    } else if (changed.length > MAXP) {
      diagnoses.push({ sig, kind: 'too-many-params', params: changed.length, hits: group.length });
    } else {
      diagnoses.push({ sig, kind: 'exact-repeat', hits: group.length });
    }
  }
  candidates.sort((a, b) => a.paramIdxs.length - b.paramIdxs.length || b.hits - a.hits);
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
    for (const cand of candidates.slice(0, 6)) {
      let paramIdxs = cand.paramIdxs;
      let v;
      for (let widen = 0; widen < 4; widen++) {
        v = symbolicPeriod(m, k, macro, cand.snap, paramIdxs);
        if (v.result !== 'widen' || paramIdxs.length >= MAXP + 2) break;
        paramIdxs = [...paramIdxs, v.position].sort((a, b) => a - b);
      }
      if (v.result === 'rule') {
        const all = counts(cand.snap);
        const n1 = paramIdxs.map((j) => all[j]);
        const rule = { A: v.A, d: v.d, n0: v.n0 };
        const note = {
          k, kind: 'rule', hits: cand.hits, paramIdxs, n1: n1.map(String),
          rule: ruleStr(rule), stepsPerPeriod: exprStr(v.steps),
          config: formatConfig(cand.snap.left, cand.snap.right, cand.snap.facing, cand.snap.q, k),
        };
        notes.push(note);
        if (ruleProvesNonhalt(rule, n1)) {
          return {
            verdict: 'nonhalt',
            cert: {
              type: 'inductive-rule', k,
              config: note.config, paramIdxs,
              A: v.A.map((row) => row.map(String)), d: v.d.map(String),
              n0: v.n0.map(String), n1: n1.map(String),
              stepsPerPeriod: exprStr(v.steps),
              reachedAt: { ops: cand.snap.ops, steps: String(cand.snap.steps) },
            },
            notes,
          };
        }
      } else if (v.result === 'proof-runaway' || v.result === 'proof-confined') {
        return { verdict: 'nonhalt', cert: { type: v.result, k }, notes };
      } else {
        notes.push({ k, kind: v.result, hits: cand.hits, params: paramIdxs.length });
      }
    }
    if (edges.length === 0) notes.push({ k, kind: 'no-edge-visits' });
  }
  return { verdict: 'open', notes };
}
