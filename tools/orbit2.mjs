// Print the orbit's boundary-event strings: every iterate where the
// glyph multiset of {a's} changes or within N of death.
const RULES = {
  'F<': { e: ['e', 'F<'], f: ['f', 'A<'], O: ['e', 'E>'], a: ['f', 'E>'] },
  'A<': { O: ['f', 'C<'], f: ['f', 'C<'], e: ['a', 'E>'], a: ['a', 'E>'] },
  'C<': { a: ['a', 'C<'], f: ['f', 'F<'], O: ['f', 'E>'], e: ['f', 'D<'] },
  'D<': { O: ['e', 'C>'], a: ['f', 'C>'], e: ['O', 'C>'] },
  'C>': { f: ['f', 'F<'] },
  'E>': { e: ['a', 'E>'], a: ['e', 'E>'], f: ['O', 'E>'], O: ['f', 'E>'] },
};
function dip(W) {
  const Z = W.slice();
  let st = 'F<', i = 0;
  for (let ops = 0; ops < 10 * Z.length + 50; ops++) {
    if (i < 0) { Z[0] = 'f'; return Z; }
    if (i >= Z.length) return { death: true, Z };
    const rule = RULES[st]?.[Z[i]];
    if (!rule) return { death: true, Z };
    Z[i] = rule[0]; st = rule[1];
    i += st.endsWith('<') ? 1 : -1;
  }
  return { death: true, Z };
}
const w = Number(process.argv[2] ?? 6);
let W = ['f', ...Array(w).fill('O'), 'a', 'a'];
let hist = [];
for (let k = 1; k <= 1e7; k++) {
  const r = dip(W);
  hist.push(W.join(''));
  if (r.death) {
    console.log(`death at iterate ${k}`);
    for (let j = Math.max(0, hist.length - 6); j < hist.length; j++) console.log(`  ${j}: ${hist[j]}`);
    break;
  }
  const before = W.filter((g) => g === 'a').length;
  W = r;
  const after = W.filter((g) => g === 'a').length;
  const posA = W.map((g, i) => (g === 'a' ? i : -1)).filter((i) => i >= 0).join(',');
  if (after !== before) console.log(`iterate ${k}: a-count ${before}->${after}  a@[${posA}]  ${W.join('')}`);
}
