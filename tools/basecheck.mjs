// From the real machine at step 354540 (the base anchor), run BOTH the
// raw machine and the abstract dip iteration for many sweeps and compare
// anchor strings — does the dip machine own the structured era from here?
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const rows = CODE.split('_');
const QN = 'ABCDEF';
const RAW = { a: '1101', O: '0101', f: '1111', e: '0111' };
const GLYPH_OF = Object.fromEntries(Object.entries(RAW).map(([g, s]) => [s, g]));
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
// raw run from c0, collecting anchors after step 354539
const tape = new Map();
let pos = 0, q = 0, steps = 0, maxNZ = -1, minNZ = 1;
const SWEEPS = Number(process.argv[2] ?? 3000);
let W = null, tail = null, ok = 0, bad = 0, firstBad = null, sweeps = 0;
while (sweeps < SWEEPS && steps < 3e8) {
  const s = tape.get(pos) ?? 0;
  const tr = rows[q].slice(s * 3, s * 3 + 3);
  if (tr === '---') { console.log(`HALT at ${steps}`); break; }
  tape.set(pos, +tr[0]);
  if (tr[0] === '1') { if (pos > maxNZ) maxNZ = pos; if (pos < minNZ) minNZ = pos; }
  else if (pos === maxNZ) { while (maxNZ >= minNZ && (tape.get(maxNZ) ?? 0) === 0) maxNZ--; }
  pos += tr[1] === 'R' ? 1 : -1;
  q = QN.indexOf(tr[2]);
  steps++;
  if (steps > 354539 && QN[q] === 'C' && pos === maxNZ + 1 && ((pos % 4) + 4) % 4 === 0) {
    const b0 = Math.floor(minNZ / 4), bN = pos / 4 - 1;
    const blocks = [];
    let clean = true;
    for (let b = b0; b <= bN; b++) {
      const g = GLYPH_OF[[0, 1, 2, 3].map((j) => tape.get(4 * b + j) ?? 0).join('')];
      if (!g) { clean = false; break; }
      blocks.push(g);
    }
    if (!clean) continue;
    if (blocks[blocks.length - 1] !== 'O') continue;
    let t = blocks.length - 2;
    while (t >= 0 && blocks[t] === 'e') t--;
    if (blocks[t] !== 'f') continue;
    const newTail = blocks.length - 2 - t;
    const newW = blocks.slice(0, t + 1).reverse();
    if (W !== null) {
      // predict: dip of old W, tail+1
      const pred = dip(W);
      if (pred && pred.join('') === newW.join('') && newTail === tail + 1) ok++;
      else {
        bad++;
        if (!firstBad) firstBad = { sweep: sweeps, predicted: pred ? pred.join('') : 'NULL', got: newW.join(''), predTail: tail + 1, gotTail: newTail };
      }
    }
    W = newW; tail = newTail; sweeps++;
  }
}
console.log(`sweeps compared: ${sweeps}, dip-exact: ${ok}, mismatch: ${bad}`);
if (firstBad) console.log(JSON.stringify(firstBad, null, 1).slice(0, 800));
