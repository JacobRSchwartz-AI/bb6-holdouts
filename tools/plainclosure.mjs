// Is the plain lattice family dip-closed? spell(v,G): cell0=O; groups m:
// [bit_{4m}, win(4m+1), win(4m+2)]; partial top group [bit_{4G}, win(4G+1)].
// Walk order: sep, cell0, cells..., inner a, outer a.
const GL = ['O', 'e', 'a', 'f'];
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
    if (i >= Z.length) return null;
    const rule = RULES[st]?.[Z[i]];
    if (!rule) return null;
    Z[i] = rule[0]; st = rule[1];
    i += st.endsWith('<') ? 1 : -1;
  }
  return null;
}
const bit = (v, b) => (v >> BigInt(b)) & 1n;
const win = (v, s) => Number((v >> BigInt(s)) & 3n);
function spell(v, G) {   // full groups 0..G-1 + partial [bit4G, win(4G+1)]
  const cells = ['O'];
  for (let m = 0; m < G; m++) {
    cells.push(bit(v, 4 * m) ? 'f' : 'O');
    cells.push(GL[win(v, 4 * m + 1)]);
    cells.push(GL[win(v, 4 * m + 2)]);
  }
  cells.push(bit(v, 4 * G) ? 'f' : 'O');
  cells.push(GL[win(v, 4 * G + 1)]);
  return ['f', ...cells, 'a', 'a'];
}
const G = Number(process.argv[2] ?? 3);          // capacity: win(4G+1) tops at v < 2^(4G+3)
const CAP = 1n << BigInt(4 * G + 3);
const LIM = BigInt(process.argv[3] ?? 70000);
let ok = 0, bad = 0, firstBad = null;
const check = (v) => {
  const got = dip(spell(v, G));
  const vn = v + 1n === CAP ? 0n : v + 1n;
  const want = spell(vn, G);
  const g = got ? got.join('') : 'NULL';
  if (g === want.join('')) ok++;
  else { bad++; if (!firstBad) firstBad = { v: v.toString(), got: g, want: want.join('') }; }
};
for (let v = 0n; v < (LIM < CAP ? LIM : CAP); v++) check(v);
// targeted deep-carry + wrap values
for (const v of [CAP - 1n, CAP - 2n, (CAP >> 1n) - 1n, (CAP >> 2n) - 1n, 3n * (CAP >> 2n) - 1n]) if (v >= 0n && v < CAP) check(v);
console.log(`G=${G} cap=${CAP}: ok=${ok} bad=${bad}`);
if (firstBad) console.log(JSON.stringify(firstBad));
