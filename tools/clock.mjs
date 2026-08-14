// Exact step-clock instrumentation (N_halt groundwork): raw-run from c0
// through the W_BASE anchor (step 354,540), then record per-sweep cost
// (steps between consecutive 4-aligned anchors) and the abstract dip's
// crossing depth for the same sweep. Goal: an exact integer law
// cost(nu) = f(tail n, depth) with residual 0 across all sweeps.
// Usage: node tools/clock.mjs [sweeps]
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const rows = CODE.split('_');
const QN = 'ABCDEF';
const SWEEPS = Number(process.argv[2] ?? 3000);

// raw machine on a growable typed tape
const MARGIN = 1024;
let cap = 1 << 20, tape = new Uint8Array(cap);
let pos = MARGIN, q = 0, steps = 0, maxNZ = MARGIN - 1;

const instep = {
  F: { e: ['e', 'F'], f: ['f', 'A'], O: ['e', 'E'], a: ['f', 'E'] },
  A: { O: ['f', 'C'], f: ['f', 'C'], e: ['a', 'E'], a: ['a', 'E'] },
  C: { a: ['a', 'C'], f: ['f', 'F'], O: ['f', 'E'], e: ['f', 'D'] },
  D: { O: ['e', 'Cr'], a: ['f', 'Cr'], e: ['O', 'Cr'] },
};
const toggle = { O: 'f', f: 'O', e: 'a', a: 'e' };
const inward = (s) => s === 'F' || s === 'A' || s === 'C' || s === 'D';
// abstract dip with depth metrics: crossings = cells consumed inward,
// bounces = Cr redips
function dipStats(W) {
  let s = 'F', di = 0, shallow = [], bounces = 0;
  const rc = {};
  const deep = [...W];
  let fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') {
      const out = deep.slice(di);
      for (const g of shallow) out.unshift(toggle[g]);
      return { out, crossings: shallow.length, bounces, rc };
    }
    if (s === 'Cr') { if (shallow[0] === 'f') { s = 'F'; bounces++; continue; } return { fail: 'Cr' }; }
    if (di >= deep.length) return { dies: s === 'C' };
    const g = deep[di], tr = instep[s]?.[g];
    if (!tr) return { fail: `${s}/${g}` };
    rc[s + g] = (rc[s + g] ?? 0) + 1;
    const [g2, s2] = tr;
    if (inward(s2)) { shallow.unshift(g2); di++; } else { deep[di] = g2; }
    s = s2;
  }
  return { fail: 'fuel' };
}

const RAW = { a: '1101', O: '0101', f: '1111', e: '0111' };
const GLYPH_OF = Object.fromEntries(Object.entries(RAW).map(([g, s]) => [s, g]));
const parseZone = () => {
  // glyph string W (head=shallowest) + tail (e-run) from the raw tape
  const blocks = [];
  for (let b = 0; b <= (maxNZ - MARGIN) >> 2; b++) {
    blocks.push(GLYPH_OF[[0, 1, 2, 3].map((j) => tape[MARGIN + 4 * b + j]).join('')] ?? '?');
  }
  let t = blocks.length - 2; // [.., tail e's, O(edge)]
  let ntail = 0;
  while (t >= 0 && blocks[t] === 'e') { t--; ntail++; }
  return { W: blocks.slice(0, t + 1).reverse(), ntail };
};

let lastAnchorSteps = -1, nu = null, W = null, rowsOut = [];
let done = false;
while (!done) {
  if (q === 2 /* C */ && pos === maxNZ + 1 && (pos - MARGIN) % 4 === 0 && maxNZ >= MARGIN && steps >= 354540) {
    if (lastAnchorSteps < 0) {
      ({ W } = ((z) => z)(parseZone().W) ? parseZone() : null);
      const z = parseZone();
      W = z.W; nu = z.ntail + 2;
      if (steps !== 354540) { console.log('unexpected first anchor', steps); break; }
    } else {
      const cost = steps - lastAnchorSteps;
      const st = dipStats(W);
      if (!st.out) { console.log('dip fail at nu', nu, st); break; }
      W = ['f', ...st.out.slice(1)];
      nu += 1;
      rowsOut.push({ nu, cost, n: nu - 2, crossings: st.crossings, bounces: st.bounces, rc: st.rc });
      const z = parseZone();
      if (z.W.join('') !== W.join('')) { console.log(`ZONE MISMATCH at nu=${nu}`); break; }
      if (z.ntail + 2 !== nu) { console.log(`TAIL MISMATCH at nu=${nu}: ${z.ntail + 2}`); break; }
      if (rowsOut.length >= SWEEPS) done = true;
    }
    lastAnchorSteps = steps;
  }
  const s = tape[pos];
  const tr = rows[q].slice(s * 3, s * 3 + 3);
  if (tr === '---') { console.log(`HALT at ${steps}`); break; }
  tape[pos] = +tr[0];
  if (+tr[0] === 1 && pos > maxNZ) maxNZ = pos;
  else if (+tr[0] === 0 && pos === maxNZ) { while (maxNZ >= MARGIN && tape[maxNZ] === 0) maxNZ--; }
  pos += tr[1] === 'R' ? 1 : -1;
  if (pos >= cap) { const t2 = new Uint8Array(cap * 2); t2.set(tape); tape = t2; cap *= 2; }
  q = QN.indexOf(tr[2]);
  steps++;
}

// exact law: cost = A + B*n + D*bounces + sum_rule w_rule*count(rule).
// Solve by exact Gaussian elimination over rationals (BigInt fractions),
// then verify residual 0 on ALL rows.
const RULES = [...new Set(rowsOut.flatMap((r) => Object.keys(r.rc)))].sort();
const feats = (r) => [1n, BigInt(r.n), BigInt(r.bounces), ...RULES.map((k) => BigInt(r.rc[k] ?? 0))];
const NF = 3 + RULES.length;
// build normal-equations-free: pick NF independent rows by elimination
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
class Frac {
  constructor(n, d = 1n) { if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; this.n = n / g; this.d = d / g; }
  add(o) { return new Frac(this.n * o.d + o.n * this.d, this.d * o.d); }
  sub(o) { return new Frac(this.n * o.d - o.n * this.d, this.d * o.d); }
  mul(o) { return new Frac(this.n * o.n, this.d * o.d); }
  div(o) { return new Frac(this.n * o.d, this.d * o.n); }
  isZero() { return this.n === 0n; }
}
const M = []; // rows: [feats..., cost] as Frac, kept in echelon form
const pivots = [];
for (const r of rowsOut) {
  let v = [...feats(r).map((x) => new Frac(x)), new Frac(BigInt(r.cost))];
  for (let i = 0; i < M.length; i++) {
    const p = pivots[i];
    if (!v[p].isZero()) v = v.map((x, j) => x.sub(M[i][j].mul(v[p])));
  }
  const p = v.findIndex((x, j) => j < NF && !x.isZero());
  if (p >= 0) { v = v.map((x) => x.div(v[p])); M.push(v); pivots.push(p); }
  else if (!v[NF].isZero()) { console.log('INCONSISTENT at nu=' + r.nu); break; }
}
console.log(`rank ${M.length} of ${NF} features (${RULES.length} rules seen)`);
// back-substitute to a particular solution (free vars = 0)
const w = Array(NF).fill(null).map(() => new Frac(0n));
for (let i = M.length - 1; i >= 0; i--) {
  let val = M[i][NF];
  for (let j = 0; j < NF; j++) if (j !== pivots[i] && !M[i][j].isZero()) val = val.sub(M[i][j].mul(w[j]));
  w[pivots[i]] = val;
}
const names = ['const', 'n', 'bounces', ...RULES];
console.log('weights:', names.map((nm, i) => `${nm}=${w[i].n}${w[i].d === 1n ? '' : '/' + w[i].d}`).join(' '));
let bad = 0;
for (const r of rowsOut) {
  const f = feats(r);
  let acc = new Frac(0n);
  for (let i = 0; i < NF; i++) acc = acc.add(w[i].mul(new Frac(f[i])));
  if (acc.d !== 1n || acc.n !== BigInt(r.cost)) bad++;
}
console.log(`sweeps measured: ${rowsOut.length}; residual-0 check: ${bad === 0 ? 'ALL EXACT' : bad + ' bad'}`);
// dump for offline analysis
import { writeFileSync } from 'node:fs';
writeFileSync('data/clock-sweeps.json', JSON.stringify(rowsOut));
console.log('dumped data/clock-sweeps.json');
