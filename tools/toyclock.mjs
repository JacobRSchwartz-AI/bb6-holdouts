// Toy validation of the exact step clock: seed a toy odometer, raw-run
// to HALT, check the clock law (weights from tools/clock.mjs) gives
// residual 0 on every complete sweep, and report the fatal partial
// cost with its tail length — the last unknown of the N_halt formula.
// Usage: node tools/toyclock.mjs <layout> <n0>   e.g. aaOOOOOOf 8
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const rows = CODE.split('_');
const QN = 'ABCDEF';
const RAW = { a: '1101', O: '0101', f: '1111', e: '0111' };
const GLYPH_OF = Object.fromEntries(Object.entries(RAW).map(([g, s]) => [s, g]));

const layout = process.argv[2];
const n0 = Number(process.argv[3] ?? 8);
const MARGIN = 64;
const cells = [...layout, ...Array(n0).fill('e'), 'O'];
let cap = 1 << 20, tape = new Uint8Array(cap);
cells.forEach((g, bi) => [...RAW[g]].forEach((c, j) => { tape[MARGIN + 4 * bi + j] = +c; }));
let pos = MARGIN + 4 * cells.length, q = QN.indexOf('C'), steps = 0, maxNZ = MARGIN + 4 * cells.length - 1;
while (tape[maxNZ] === 0) maxNZ--;

const instep = {
  F: { e: ['e', 'F'], f: ['f', 'A'], O: ['e', 'E'], a: ['f', 'E'] },
  A: { O: ['f', 'C'], f: ['f', 'C'], e: ['a', 'E'], a: ['a', 'E'] },
  C: { a: ['a', 'C'], f: ['f', 'F'], O: ['f', 'E'], e: ['f', 'D'] },
  D: { O: ['e', 'Cr'], a: ['f', 'Cr'], e: ['O', 'Cr'] },
};
const toggle = { O: 'f', f: 'O', e: 'a', a: 'e' };
const inward = (s) => s === 'F' || s === 'A' || s === 'C' || s === 'D';
function dipStats(W) {
  let s = 'F', di = 0, shallow = [], bounces = 0;
  const rc = {};
  const deep = [...W];
  let fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') {
      const out = deep.slice(di);
      for (const g of shallow) out.unshift(toggle[g]);
      return { out, bounces, rc };
    }
    if (s === 'Cr') { if (shallow[0] === 'f') { s = 'F'; bounces++; continue; } return { fail: 'Cr' }; }
    if (di >= deep.length) return { dies: s === 'C', rc, bounces };
    const g = deep[di], tr = instep[s]?.[g];
    if (!tr) return { fail: `${s}/${g}` };
    rc[s + g] = (rc[s + g] ?? 0) + 1;
    const [g2, s2] = tr;
    if (inward(s2)) { shallow.unshift(g2); di++; } else { deep[di] = g2; }
    s = s2;
  }
  return { fail: 'fuel' };
}

// clock law from tools/clock.mjs (residual 0 over 3000 real-machine sweeps)
const W8 = { const: 56, n: 16, bounces: 4, Aa: 16, Ae: 12, Af: 24, CO: -4, Ca: 8, Fe: 8 };
const lawCost = (n, st) => W8.const + W8.n * n + W8.bounces * (st.bounces ?? 0)
  + Object.entries(st.rc).reduce((a, [k, c]) => a + (W8[k] ?? 0) * c, 0);

const parseZone = () => {
  const blocks = [];
  for (let b = 0; b <= (maxNZ - MARGIN) >> 2; b++) {
    blocks.push(GLYPH_OF[[0, 1, 2, 3].map((j) => tape[MARGIN + 4 * b + j]).join('')] ?? '?');
  }
  let t = blocks.length - 2, ntail = 0;
  while (t >= 0 && blocks[t] === 'e') { t--; ntail++; }
  return { W: blocks.slice(0, t + 1).reverse(), ntail };
};

let lastAnchorSteps = 0, nu = n0 + 2, sweeps = 0, bad = 0;
let { W } = parseZone();
let halted = false;
while (!halted) {
  const s = tape[pos];
  const tr = rows[q].slice(s * 3, s * 3 + 3);
  if (tr === '---') { halted = true; break; }
  tape[pos] = +tr[0];
  if (+tr[0] === 1 && pos > maxNZ) maxNZ = pos;
  else if (+tr[0] === 0 && pos === maxNZ) { while (maxNZ >= MARGIN && tape[maxNZ] === 0) maxNZ--; }
  pos += tr[1] === 'R' ? 1 : -1;
  if (pos >= cap) { const t2 = new Uint8Array(cap * 2); t2.set(tape); tape = t2; cap *= 2; }
  q = QN.indexOf(tr[2]);
  steps++;
  if (q === 2 && pos === maxNZ + 1 && (pos - MARGIN) % 4 === 0 && maxNZ >= MARGIN) {
    const cost = steps - lastAnchorSteps;
    const st = dipStats(W);
    if (!st.out) { console.log('unexpected dip result mid-run', st); break; }
    W = ['f', ...st.out.slice(1)];
    nu += 1; sweeps++;
    if (lawCost(nu - 2, st) !== cost) {
      bad++;
      if (bad <= 5) console.log(`law MISS at nu=${nu}: cost=${cost} law=${lawCost(nu - 2, st)}`);
    }
    const z = parseZone();
    if (z.W.join('') !== W.join('')) { console.log(`zone mismatch nu=${nu}`); break; }
    lastAnchorSteps = steps;
  }
}
console.log(`halted at raw step ${steps}; complete sweeps: ${sweeps}; law misses: ${bad}`);
const st = dipStats(W);
console.log(`dying dip: dies=${st.dies}, bounces=${st.bounces}, rc=${JSON.stringify(st.rc)}`);
const fatal = steps - lastAnchorSteps;
const nDying = nu - 2;
console.log(`fatal partial cost = ${fatal}, dying-anchor tail n = ${nDying}`);
console.log(`fatal - 4n = ${fatal - 4 * nDying}`);
