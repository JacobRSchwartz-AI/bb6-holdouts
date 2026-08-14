// Iterate dip from a seed string until the orbit repeats or dies.
// Report: orbit length, distinct boundary shapes, death or cycle.
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
    if (i >= Z.length) return { death: 'fell off left end', Z };
    const rule = RULES[st]?.[Z[i]];
    if (!rule) return { death: `no rule ${st} ${Z[i]}`, Z };
    Z[i] = rule[0]; st = rule[1];
    i += st.endsWith('<') ? 1 : -1;
  }
  return { death: 'nonterm', Z };
}
const w = Number(process.argv[2] ?? 6);   // zone cells incl. cell0
const LIM = Number(process.argv[3] ?? 100000);
let W = ['f', ...Array(w).fill('O'), 'a', 'a'];
const seen = new Map();
seen.set(W.join(''), 0);
for (let k = 1; k <= LIM; k++) {
  const r = dip(W);
  if (r.death) { console.log(`DEATH at iterate ${k}: ${r.death}\n  last: ${W.join('')}`); process.exit(0); }
  W = r;
  const key = W.join('');
  if (seen.has(key)) {
    console.log(`CYCLE: iterate ${k} equals iterate ${seen.get(key)} (period ${k - seen.get(key)})`);
    console.log(`  state: ${key}`);
    process.exit(0);
  }
  seen.set(key, k);
  if (k <= 3 || k % 20000 === 0) console.log(`${k}: ${key}`);
}
console.log(`no cycle, no death in ${LIM} iterates; final: ${W.join('')}`);
