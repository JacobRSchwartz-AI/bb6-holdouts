import { writeFileSync } from 'node:fs';
import { parseMachine } from '../src/machine.mjs';
import { runMacro, makeMacro } from '../src/macro.mjs';
import { proveLocal, CONTEXT } from '../src/family.mjs';
import { exprStr } from '../src/symbolic.mjs';

// Milestone 1: the machine's complete local rulebook. Enumerate every
// observed anchor-tail template, prove the one-sweep lemma for each with
// big counts symbolic and everything deeper abstracted as CONTEXT, then
// measure what fraction of all observed sweep transitions the proven
// rulebook explains. Adaptive window: widen on context-touched.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const K_BLOCK = 4;
const STATE_C = 2;
const WIDTHS = [5, 8, 12, 999];   // 999 = whole config, no context marker
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

const cls = (c) => (c <= 5n ? String(c) : 'big');
const tmplKey = (L, w) => L.slice(Math.max(0, L.length - w)).map(([b, c]) => `${b}:${cls(c)}`).join(' ');

const ev = (e, vals) => e.c.reduce((a, v, i) => a + v * vals[i], e.b);

function buildPre(tail, withContext) {
  const params = [];
  tail.forEach(([, c], i) => { if (cls(c) === 'big') params.push(i); });
  const dim = params.length;
  const K0 = (b) => ({ c: new Array(dim).fill(0n), b });
  const U = (j) => ({ c: new Array(dim).fill(0n).map((_, i) => (i === j ? 1n : 0n)), b: 0n });
  const left = withContext ? [[CONTEXT, K0(1n)]] : [];
  tail.forEach(([b, c], i) => {
    const j = params.indexOf(i);
    left.push([b, j >= 0 ? U(j) : K0(c)]);
  });
  return { pre: { left, right: [], q: STATE_C, facing: 'R', steps: K0(0n), n0: new Array(dim).fill(1n) }, params };
}

function proveTemplate(tail, withContext) {
  const { pre, params } = buildPre(tail, withContext);
  const r = proveLocal(m, K_BLOCK, macro, pre, {
    until: (s) => s.q === STATE_C && s.facing === 'R' && s.right.length === 0,
    maxHops: 64,
  });
  if (r.result !== 'proved') return { result: r.result };
  return { result: 'proved', params, post: r.state.left, steps: r.state.steps, n0: r.state.n0 };
}

// group anchor indices by widest-needed template, prove each template once
const lemmas = new Map();   // key -> {tail, width, proof|failure, count}
const pairFail = { unexplained: 0, mismatch: 0 };
let explained = 0;

for (let i = 0; i < anchors.length - 1; i++) {
  const L = anchors[i];
  let lemma = null;
  for (const w of WIDTHS) {
    const withContext = w < L.length;
    const eff = Math.min(w, L.length);
    const key = `w${eff}|${withContext ? 'ctx' : 'full'}|${tmplKey(L, eff)}`;
    if (!lemmas.has(key)) {
      const tail = L.slice(L.length - eff).map(([b, c]) => [b, c]);
      const p = proveTemplate(tail, withContext);
      lemmas.set(key, { tail, width: eff, withContext, proof: p, count: 0 });
    }
    const entry = lemmas.get(key);
    if (entry.proof.result === 'proved') {
      const tailNow = L.slice(L.length - entry.width);
      const valsNow = entry.proof.params.map((pi) => tailNow[pi][1]);
      if (entry.proof.n0.every((b, j) => valsNow[j] >= b)) { lemma = entry; entry.count++; break; }
    }
    if (!withContext) break;
  }
  if (!lemma) {
    pairFail.unexplained++;
    if (pairFail.samples === undefined) pairFail.samples = [];
    if (pairFail.samples.length < 6) {
      const w = Math.min(999, L.length);
      const entry = lemmas.get(`w${w}|full|${tmplKey(L, w)}`);
      pairFail.samples.push({
        i, N: L.length >= 2 ? L[L.length - 2][1] : 0n, len: L.length,
        fullResult: entry?.proof.result,
        tail: L.slice(-6).map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${c}`).join(' '),
      });
    }
    continue;
  }

  const { proof, width } = lemma;
  const tail = L.slice(L.length - width);
  const vals = proof.params.map((pi) => tail[pi][1]);
  const predicted = proof.post.slice(lemma.withContext ? 1 : 0).map(([b, c]) => [b, ev(c, vals)]);
  const next = anchors[i + 1];
  const actualTail = next.slice(next.length - predicted.length);
  const match = predicted.length === actualTail.length &&
    predicted.every(([b, c], k) => b === actualTail[k][0] && c === actualTail[k][1]);
  if (match) explained++;
  else pairFail.mismatch++;
}

const proved = [...lemmas.values()].filter((l) => l.proof.result === 'proved');
const failed = [...lemmas.values()].filter((l) => l.proof.result !== 'proved');
const pairs = anchors.length - 1;
console.log(`\nrulebook: ${proved.length} proven lemmas (${failed.length} template failures)`);
console.log(`coverage: ${explained}/${pairs} transitions explained (${(explained / pairs * 100).toFixed(3)}%)`);
console.log(`unexplained: ${pairFail.unexplained}, MISMATCHES (must be 0): ${pairFail.mismatch}`);
const failHist = {};
for (const l of failed) failHist[l.proof.result] = (failHist[l.proof.result] ?? 0) + 1;
console.log('template failure kinds:', JSON.stringify(failHist));
for (const s of pairFail.samples ?? []) console.log(`  unexplained @N=${s.N} len=${s.len} full=${s.fullResult}: … ${s.tail}`);

proved.sort((a, b) => b.count - a.count);
const lines = [];
for (const l of proved) {
  lines.push(`LEMMA w=${l.width} used=${l.count}`);
  lines.push(`  pre : CTX ${l.tail.map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${cls(c) === 'big' ? 'n' : c}`).join(' ')}`);
  lines.push(`  post: ${l.proof.post.map(([b, c]) => `${b === CONTEXT ? 'CTX' : b.toString(2).padStart(4, '0')}^${exprStr(c)}`).join(' ')}`);
  lines.push(`  steps=${exprStr(l.proof.steps)}  side: n >= [${l.proof.n0.join(',')}]`);
}
for (const l of failed.slice(0, 10)) {
  lines.push(`FAILED (${l.proof.result}) w=${l.width}: CTX ${l.tail.map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${cls(c) === 'big' ? 'n' : c}`).join(' ')}`);
}
writeFileSync('data/rulebook.txt', lines.join('\n') + '\n');
console.log(`\ntop-5 workhorse lemmas:`);
for (const l of proved.slice(0, 5)) {
  console.log(`  used ${l.count}×: CTX ${l.tail.map(([b, c]) => `${b.toString(2).padStart(4, '0')}^${cls(c) === 'big' ? 'n' : c}`).join(' ')}`);
  console.log(`    -> ${l.proof.post.slice(0, 8).map(([b, c]) => `${b === CONTEXT ? 'CTX' : b.toString(2).padStart(4, '0')}^${exprStr(c)}`).join(' ')}${l.proof.post.length > 8 ? ' …' : ''}`);
}
