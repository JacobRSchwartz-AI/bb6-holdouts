// Oracle for the post-crisis ladder (P-2026-08-15-q): the abstract dip
// (instep table transcribed from coq/OdometerDip.v) applied to the eight
// width-213 crisis strings. Rungs 0..6 must map T(h)@vlow=ones to
// T(h+1)@vlow=0; rung 7 must die (C falls off the left end).
const instep = {
  F: { e: ['e', 'F'], f: ['f', 'A'], O: ['e', 'E'], a: ['f', 'E'] },
  A: { O: ['f', 'C'], f: ['f', 'C'], e: ['a', 'E'], a: ['a', 'E'] },
  C: { a: ['a', 'C'], f: ['f', 'F'], O: ['f', 'E'], e: ['f', 'D'] },
  D: { O: ['e', 'Cr'], a: ['f', 'Cr'], e: ['O', 'Cr'] },
};
const toggle = { O: 'f', f: 'O', e: 'a', a: 'e' };
const inward = (s) => ['F', 'A', 'C', 'D'].includes(s);

// head of deep = current (shallowest unvisited); head of shallow = last crossed
function dip(W) {
  let s = 'F', deep = [...W], shallow = [];
  let fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') {
      for (const g of shallow) deep.unshift(toggle[g]);
      return { out: deep };
    }
    if (s === 'Cr') {
      if (shallow[0] === 'f') { s = 'F'; continue; }
      return { fail: 'Cr without f' };
    }
    if (deep.length === 0) return s === 'C' ? { dies: true } : { fail: `falloff ${s}` };
    const g = deep[0], tr = instep[s]?.[g];
    if (!tr) return { fail: `no rule ${s}/${g}` };
    const [g2, s2] = tr;
    if (inward(s2)) { deep.shift(); shallow.unshift(g2); }
    else { deep[0] = g2; }
    s = s2;
  }
  return { fail: 'fuel' };
}

const tops = [
  ['O', 'O', 'a', 'a'], ['f', 'O', 'a', 'a'],
  ['O', 'e', 'a', 'a'], ['f', 'e', 'a', 'a'],
  ['O', 'a', 'f', 'a'], ['f', 'a', 'f', 'a'],
  ['O', 'f', 'f', 'a'], ['f', 'f', 'f', 'a'],
];
let pass = 0;
for (let h = 0; h < 7; h++) {
  const W = ['f', 'O', ...Array(210).fill('f'), ...tops[h]];
  const r = dip(W);
  const expect = ['O', 'O', ...Array(210).fill('O'), ...tops[h + 1]];
  const ok = r.out && r.out.length === expect.length && r.out.every((g, i) => g === expect[i]);
  console.log(`rung ${h}->${h + 1}: ${ok ? 'OK' : 'MISMATCH ' + JSON.stringify(r).slice(0, 300)}`);
  if (ok) pass++;
}
const W7 = ['f', 'O', ...Array(210).fill('f'), ...tops[7]];
const r7 = dip(W7);
console.log(`rung 7->8: ${r7.dies ? 'DIES (OK)' : 'MISMATCH ' + JSON.stringify(r7).slice(0, 300)}`);
if (r7.dies) pass++;
console.log(pass === 8 ? 'ALL 8 PASS' : `FAIL: ${pass}/8`);
