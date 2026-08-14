// Phase A census (P-2026-08-14-n): run the raw machine from c0 and log
// every distinct block-boundary transition — (entry state/side, content)
// -> (exit state/side, content') — over 4-cell blocks on the absolute
// grid. The distinct-signature list is the Coq in-walk case list.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const rows = CODE.split('_');
const QN = 'ABCDEF';
const MAXSTEPS = Number(process.argv[2] ?? 1e7);

const tape = new Map();
let pos = 0, q = 0, steps = 0;
const blockOf = (p) => Math.floor(p / 4);
const content = (b) => [0, 1, 2, 3].map((j) => tape.get(4 * b + j) ?? 0).join('');

const GLYPH_OF = { '0101': 'O', '0111': 'e', '1101': 'a', '1111': 'f' };
const gname = (c) => GLYPH_OF[c] ?? `[${c}]`;

let curBlock = 0;
let entry = { q: QN[q], side: 'L', content: content(0), step: 0 };
const census = new Map();
const emit = (exitQ, exitSide, exitContent) => {
  const sig = `${entry.q}${entry.side === 'L' ? '>' : '<'} ${gname(entry.content)} -> ${gname(exitContent)} ${exitQ}${exitSide === 'R' ? '>' : '<'}`;
  let rec = census.get(sig);
  if (!rec) census.set(sig, (rec = { n: 0, first: steps, last: 0 }));
  rec.n++; rec.last = steps;
};

while (steps < MAXSTEPS) {
  const s = tape.get(pos) ?? 0;
  const tr = rows[q].slice(s * 3, s * 3 + 3);
  if (tr === '---') { console.log(`HALT at ${steps}`); process.exit(1); }
  tape.set(pos, +tr[0]);
  pos += tr[1] === 'R' ? 1 : -1;
  q = QN.indexOf(tr[2]);
  steps++;
  const b = blockOf(pos);
  if (b !== curBlock) {
    const exitSide = b > curBlock ? 'R' : 'L';
    emit(QN[q], exitSide, content(curBlock));
    curBlock = b;
    entry = { q: QN[q], side: exitSide === 'R' ? 'L' : 'R', content: content(b), step: steps };
  }
}

const rowsOut = [...census.entries()].sort((a, b) => b[1].n - a[1].n);
console.log(`steps=${steps}  distinct signatures=${rowsOut.length}`);
console.log('sig                              count      first-step   last-step');
for (const [sig, r] of rowsOut) {
  console.log(`${sig.padEnd(30)} ${String(r.n).padStart(10)}  ${String(r.first).padStart(10)}  ${r.last}`);
}
const late = rowsOut.filter(([, r]) => r.first > MAXSTEPS / 10);
console.log(`\nsignatures first seen after step ${MAXSTEPS / 10}: ${late.length}`);
for (const [sig, r] of late) console.log(`  ${sig}  first=${r.first}`);
const dead = rowsOut.filter(([, r]) => r.last < MAXSTEPS / 2);
console.log(`signatures last seen before step ${MAXSTEPS / 2} (era-transients?): ${dead.length}`);
for (const [sig, r] of dead) console.log(`  ${sig}  n=${r.n} last=${r.last}`);