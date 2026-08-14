// M4 glyph layer ground truth (P-2026-08-14-m). Raw-simulate the small
// analog  a² O^m f e^n O  (head at right edge, state C) and report:
//   - per-sweep: anchor parse in glyphs, cost, zone value
//   - one traced sweep: block-boundary crossings (state, direction, cost)
// Raw glyph spellings are value-bits reversed: O=0101 e=0111 a=1101 f=1111.
const CODE = '1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA';
const rows = CODE.split('_');
const QN = 'ABCDEF';
const RAW = { a: '1101', O: '0101', f: '1111', e: '0111' };
const GLYPH_OF = Object.fromEntries(Object.entries(RAW).map(([g, s]) => [s, g]));

// argv[2]: zone width m (numeric) OR an explicit layout string like
// "aafffffOfeeeeeeeeO" (one letter per block, left-to-right).
const arg2 = process.argv[2] ?? '6';
const n = Number(process.argv[3] ?? 8);
const SWEEPS = Number(process.argv[4] ?? 40);
const TRACE_SWEEP = Number(process.argv[5] ?? 3);

const layout = /^[Oeaf]+$/.test(arg2)
  ? arg2.split('')
  : ['a', 'a', ...Array(Number(arg2)).fill('O'), 'f', ...Array(n).fill('e'), 'O'];
const tape = new Map();
layout.forEach((g, bi) => RAW[g].split('').forEach((c, j) => tape.set(4 * bi + j, +c)));
let pos = 4 * layout.length, q = QN.indexOf('C'), steps = 0;

const parse = () => {
  let maxNZ = -1;
  for (const [p, v] of tape) if (v === 1 && p > maxNZ) maxNZ = p;
  const blocks = [];
  for (let b = 0; b <= maxNZ >> 2; b++) {
    const s = [0, 1, 2, 3].map((j) => tape.get(4 * b + j) ?? 0).join('');
    blocks.push(GLYPH_OF[s] ?? `[${s}]`);
  }
  return blocks;
};
const rle = (bs) => {
  const out = [];
  for (const g of bs) {
    if (out.length && out[out.length - 1][0] === g) out[out.length - 1][1]++;
    else out.push([g, 1]);
  }
  return out.map(([g, c]) => (c > 1 ? `${g}^${c}` : g)).join(' ');
};

let lastAnchorSteps = 0, sweep = 0, prevNu = null;
let traceLog = [], tracing = TRACE_SWEEP === 0;
const WATCH = Number(process.argv[6] ?? 12);   // tail block to transcribe
let watchLog = [];
while (sweep <= SWEEPS) {
  const s = tape.get(pos) ?? 0;
  const tr = rows[q].slice(s * 3, s * 3 + 3);
  if (tr === '---') { console.log(`HALT at step ${steps}`); process.exit(1); }
  tape.set(pos, +tr[0]);
  const dir = tr[1] === 'R' ? 1 : -1;
  pos += dir;
  q = QN.indexOf(tr[2]);
  steps++;
  if (tracing && pos % 4 === 0) {
    traceLog.push({ steps, block: pos / 4, q: QN[q], dir: dir > 0 ? '>' : '<' });
  }
  if (tracing && pos >= 4 * WATCH && pos < 4 * WATCH + 4) {
    const cells = [0, 1, 2, 3].map((j) => tape.get(4 * WATCH + j) ?? 0).join('');
    const last = watchLog[watchLog.length - 1];
    if (!last || last.cells !== cells || last.q !== QN[q]) watchLog.push({ steps, q: QN[q], off: pos - 4 * WATCH, cells });
  }
  let maxNZ = -1;
  for (const [p, v] of tape) if (v === 1 && p > maxNZ) maxNZ = p;
  if (QN[q] === 'C' && pos === maxNZ + 1 && pos % 4 === 0) {
    const blocks = parse();
    // tail = run of e's immediately left of the edge O; nu = tail + 2
    let tail = 0;
    for (let i = blocks.length - 2; i >= 0 && blocks[i] === 'e'; i--) tail++;
    const nu = tail + 2;
    const cost = steps - lastAnchorSteps;
    let note = '';
    if (prevNu !== null && nu === prevNu + 1) {
      let t = 0, x = sweep - 1;
      while (x & 1) { x >>= 1; t++; }
      const base = 16 * (nu - 1) + 34 + 6 * t + (t % 2 === 0 ? 2 : 0);
      note = `  cost=${cost} base(t=${t})=${base} dev=${cost - base}`;
    }
    console.log(`sweep ${sweep}: nu=${nu}  ${rle(blocks)}${note}`);
    if (tracing) {
      const compact = [];
      for (const ev of traceLog) {
        const tag = `${ev.q}${ev.dir}`;
        if (compact.length && compact[compact.length - 1].tag === tag) compact[compact.length - 1].to = ev.block;
        else compact.push({ tag, from: ev.block, to: ev.block });
      }
      console.log('  passes: ' + compact.map((c) => `${c.tag}[${c.from}..${c.to}]`).join(' '));
      console.log(`  block ${WATCH} transcript (step, state, cell-offset, cells):`);
      for (const w of watchLog) console.log(`    +${w.steps - lastAnchorSteps} ${w.q}@${w.off} ${w.cells}`);
      tracing = false; traceLog = []; watchLog = [];
    }
    if (sweep + 1 === TRACE_SWEEP) tracing = true;
    lastAnchorSteps = steps; prevNu = nu; sweep++;
  }
  if (steps > 8e7) { console.log("step cap"); break; }
}