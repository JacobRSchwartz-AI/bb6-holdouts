// P-2026-08-14-o: validate the block-level abstract dip machine against
// the raw machine. Seed a^2 O^m f e^8 O; at every anchor, extract the
// left glyph string W (walk order: sep, cell0, ..., inner a, outer a),
// run the abstract walk, and check its output equals the next anchor's W
// (and that the tail grew by exactly one e).
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const rows = CODE.split('_');
const QN = 'ABCDEF';
const RAW = { a: '1101', O: '0101', f: '1111', e: '0111' };
const GLYPH_OF = Object.fromEntries(Object.entries(RAW).map(([g, s]) => [s, g]));

const m = Number(process.argv[2] ?? 24);
const SWEEPS = Number(process.argv[3] ?? 66000);

// The abstract machine. Rules: [state, dir] x glyph -> [glyph', state', dir'].
const RULES = {
  'F<': { e: ['e', 'F<'], f: ['f', 'A<'], O: ['e', 'E>'], a: ['f', 'E>'] },
  'A<': { O: ['f', 'C<'], f: ['f', 'C<'], e: ['a', 'E>'], a: ['a', 'E>'] },
  'C<': { a: ['a', 'C<'], f: ['f', 'F<'], O: ['f', 'E>'], e: ['f', 'D<'] },
  'D<': { O: ['e', 'C>'], a: ['f', 'C>'], e: ['O', 'C>'] },
  'C>': { f: ['f', 'F<'] },
  'E>': { e: ['a', 'E>'], a: ['e', 'E>'], f: ['O', 'E>'], O: ['f', 'E>'] },
};
// Walk over W (index 0 = separator). Leftward states consume increasing
// indices; rightward states decreasing. Terminates when a rightward state
// moves past index 0. Returns null on any missing rule or fall-off.
function dipWalk(W) {
  const Z = W.slice();
  let st = 'F<', i = 0;
  for (let ops = 0; ops < 10 * Z.length + 50; ops++) {
    if (i < 0) { Z[0] = 'f'; return { Z, exit: st }; }   // sep round-trips f->O->f (sep_bounce)
    if (i >= Z.length) return null;
    const rule = RULES[st]?.[Z[i]];
    if (!rule) return { err: `no rule ${st} ${Z[i]} @${i}`, Z };
    Z[i] = rule[0];
    st = rule[1];
    i += st.endsWith('<') ? 1 : -1;
  }
  return { err: 'nonterm', Z };
}

const tape = new Map();
const layout = ['a', 'a', ...Array(m).fill('O'), 'f', ...Array(8).fill('e'), 'O'];
layout.forEach((g, bi) => RAW[g].split('').forEach((c, j) => tape.set(4 * bi + j, +c)));
let pos = 4 * layout.length, q = QN.indexOf('C'), steps = 0;

const parseAnchor = () => {
  let maxNZ = -1;
  for (const [p, v] of tape) if (v === 1 && p > maxNZ) maxNZ = p;
  const blocks = [];
  for (let b = 0; b <= maxNZ >> 2; b++) blocks.push(GLYPH_OF[[0, 1, 2, 3].map((j) => tape.get(4 * b + j) ?? 0).join('')] ?? '?');
  // blocks: a a zone... f(sep) e-tail... O(edge)
  if (blocks[blocks.length - 1] !== 'O') return null;
  let t = blocks.length - 2;
  while (t >= 0 && blocks[t] === 'e') t--;
  if (blocks[t] !== 'f') return null;
  const W = blocks.slice(0, t + 1).reverse();   // sep first, outer a last
  return { W, tail: blocks.length - 2 - t };
};

let prev = null, sweep = 0, ok = 0, bad = 0, walkErr = 0;
const depthHist = new Map();
let firstBad = null;
let maxNZ = 4 * layout.length - 1;
while (sweep < SWEEPS) {
  const s = tape.get(pos) ?? 0;
  const tr = rows[q].slice(s * 3, s * 3 + 3);
  if (tr === '---') { console.log(`HALT at ${steps}`); process.exit(1); }
  tape.set(pos, +tr[0]);
  if (tr[0] === '1' && pos > maxNZ) maxNZ = pos;
  else if (tr[0] === '0' && pos === maxNZ) { while (maxNZ >= 0 && (tape.get(maxNZ) ?? 0) === 0) maxNZ--; }
  pos += tr[1] === 'R' ? 1 : -1;
  q = QN.indexOf(tr[2]);
  steps++;
  if (QN[q] === 'C' && pos === maxNZ + 1 && pos % 4 === 0) {
    const a = parseAnchor();
    if (a && prev) {
      const walked = dipWalk(prev.W);
      if (!walked || walked.err) { walkErr++; if (!firstBad) firstBad = { sweep, err: walked?.err, W: prev.W.join('') }; }
      else {
        const match = walked.Z.join('') === a.W.join('') && a.tail === prev.tail + 1;
        if (match) ok++;
        else { bad++; if (!firstBad) firstBad = { sweep, got: walked.Z.join(''), want: a.W.join(''), pre: prev.W.join('') }; }
        let d = 0;
        while (d < walked.Z.length && walked.Z[d] === prev.W[d]) d++;
        // depth of change as a proxy for carry depth
        const dd = prev.W.findIndex((g, i) => walked.Z[i] !== g);
        depthHist.set(dd, (depthHist.get(dd) ?? 0) + 1);
      }
    }
    prev = a;
    sweep++;
  }
  if (steps > 5e9) break;
}
console.log(`sweeps=${sweep} abstract-vs-raw: ok=${ok} bad=${bad} walkErr=${walkErr}`);
if (firstBad) console.log('first bad:', JSON.stringify(firstBad));
console.log('change-depth histogram (index of shallowest changed cell):');
for (const [d, n] of [...depthHist.entries()].sort((a, b) => a[0] - b[0])) console.log(`  ${d}: ${n}`);