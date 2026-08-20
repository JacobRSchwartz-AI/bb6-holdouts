// Run-level abstract machine for the parity machine, co-verified against the
// raw simulator at every fill exit (the D1 step: D reads the terminating 1,
// F takes the excursion). The tape is two run lists over implicit blank:
// wall (top-first, left of head incl. head cell at EXC) and right (head-first).
//
// Events:
//   BE   B at a leading 1-run: skim, convert first 0, hand to CE.
//   CE   C erases the leading 1-run (len c, possibly 0), then the 0-run after
//        it (len d) decides: d=1 gap0 (safe, any c), d>=2 fill (SAFE IFF c
//        EVEN -- the halt criterion). Both land at EXC.
//   EXC  F at the wall top, right = 1.. (P1) or 0 1 .. (P0). Dispatch on the
//        top two wall cells: (1,1) carry pushes 01; (0,0)+P0 cs_body pushes
//        111; (0,0)/(0,1)+P1 bitset/bitset_odd exit to CE; (0,1)+P0 degen
//        exits to CE; (1,0) f1_to_A exits to BE.
//
//   node parity-macro.mjs 20000000          co-verify against raw
//   node parity-macro.mjs --mine 2000000    abstract-only, parity-state census
//   node parity-macro.mjs --dump 40         print first events

const args = process.argv.slice(2);
const MODE = args[0] === '--mine' ? 'mine' : args[0] === '--dump' ? 'dump'
  : args[0] === '--fills' ? 'fills' : args[0] === '--windows' ? 'windows' : 'verify';
const N = Number(args[MODE === 'verify' ? 0 : 1] ?? 2e6);

class Halt extends Error {}

class Abs {
  constructor() {
    this.wall = [[1, 1]];
    this.right = [[1, 4]];
    this.mode = 'BE';
    this.stats = { gap0: 0, fill: 0, fillOdd: 0, exits: {}, events: 0 };
  }
  wcell(i) { for (const [v, n] of this.wall) { if (i < n) return v; i -= n; } return 0; }
  wpop(k) {
    while (k > 0 && this.wall.length) {
      const t = this.wall[0], take = Math.min(k, t[1]);
      t[1] -= take; k -= take;
      if (t[1] === 0) this.wall.shift();
    }
  }
  wpush(v, n) {
    if (n <= 0) return;
    if (this.wall.length && this.wall[0][0] === v) this.wall[0][1] += n;
    else this.wall.unshift([v, n]);
  }
  rlead() { return this.right.length ? this.right[0][0] : 0; }
  rleadLen() { return this.right.length ? this.right[0][1] : Infinity; }
  rpopRun(v) {
    if (!this.right.length || this.right[0][0] !== v) return 0;
    return this.right.shift()[1];
  }
  rpopCells(k) {
    while (k > 0 && this.right.length) {
      const t = this.right[0], take = Math.min(k, t[1]);
      t[1] -= take; k -= take;
      if (t[1] === 0) this.right.shift();
    }
  }
  rpush(v, n) {
    if (n <= 0) return;
    if (this.right.length && this.right[0][0] === v) this.right[0][1] += n;
    else this.right.unshift([v, n]);
  }
  rpushSeq(cells) { for (let i = cells.length - 1; i >= 0; i--) this.rpush(cells[i], 1); }

  stepBE() {
    const a = this.rpopRun(1);
    if (!a) throw new Error('BE: right does not start with a 1-run');
    this.wpush(1, a + 1);
    this.rpopCells(1);            // the converted 0 (from blank if right ran out)
    this.mode = 'CE';
  }

  stepCE() {
    const c = this.rlead() === 1 ? this.rpopRun(1) : 0;
    const d = this.rleadLen();    // Infinity when the rest is blank
    if (this.onCE) this.onCE(c, d);
    if (d >= 2 && c % 2 === 1) { this.stats.fillOdd++; throw new Halt(`CE: odd run ${c} before 0^${d}`); }
    if (d === 1) {
      this.stats.gap0++;
      this.rpopCells(1);
      this.wpush(0, c + 1);
    } else {
      this.stats.fill++;
      if (!this.wall.length || this.wall[0][0] !== 1) throw new Error('CE fill: wall top not a 1');
      this.wall[0][1]--; if (this.wall[0][1] === 0) this.wall.shift();
      this.rpopCells(2);
      this.rpush(1, c + 3);
    }
    this.mode = 'EXC';
    this.stats.events++;
  }

  // One dispatch iteration at D1 granularity. cs_body, the first half of
  // bitset, and degen_cs proper each END at a D1 (their interior CTX-0/2
  // fill), so they checkpoint; carry / f1_to_A / bitset_odd contain no fill.
  // Returns true when this iteration ended at a D1.
  stepEXC() {
    const p0 = this.rlead() === 0;
    if (p0 && this.right.length && this.right[0][1] !== 1) throw new Error('EXC P0: leading 0-run != 1');
    if (p0 && !this.right.length) throw new Error('EXC P0: blank right');
    const a = this.wcell(0), b = this.wcell(1);
    if (a === 1 && b === 1) { this.wpop(2); this.rpushSeq([0, 1]); this.exit('carry'); return false; }
    if (a === 1 && b === 0) {
      this.wpop(2); this.wpush(1, 1); this.rpushSeq([1]); this.mode = 'BE'; this.exit('f1A'); return false;
    }
    if (a === 0 && b === 0) {
      if (p0) {                   // cs_body: 9 steps, ends at its CTX-2 fill's D1
        this.rpopCells(1); this.wpop(2); this.rpushSeq([1, 1, 1]);
        this.exit('cs'); this.stats.events++; return true;
      }
      // bitset first half: 4 steps, wall (0,0) -> (0,1), ends at a gap-0 D1
      this.wpop(2); this.wpush(1, 1); this.wpush(0, 1);
      this.exit('bit_half'); this.stats.events++; return true;
    }
    // (0,1)
    if (p0) {                     // degen_cs proper: 5 steps, ends at a gap-0 D1
      this.rpopCells(1); this.wpop(2); this.wpush(1, 2); this.wpush(0, 1);
      this.exit('degen'); this.stats.events++; return true;
    }
    // bitset_odd: 3 steps, no fill, hands C the erasure
    this.wpop(2); this.wpush(1, 2); this.mode = 'CE'; this.exit('bitset_odd'); return false;
  }
  exit(name) { this.stats.exits[name] = (this.stats.exits[name] ?? 0) + 1; }

  nextCheckpoint() {              // advance to the next D1-anchored state
    for (;;) {
      if (this.mode === 'EXC') { if (this.stepEXC()) return; }
      else if (this.mode === 'BE') this.stepBE();
      else { this.stepCE(); return; }   // CE always ends at its fill/gap0 D1
    }
  }
  snap() { return JSON.stringify({ w: this.wall, r: this.right }); }
}

// ---------- raw machine ----------
const CODE = '1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA';
const rows = CODE.split('_').map((s) => [0, 1].map((b) => {
  const e = s.slice(b * 3, b * 3 + 3);
  return e === '---' ? null : { w: +e[0], d: e[1], q: e.charCodeAt(2) - 65 };
}));

function runVerify(maxSteps) {
  const abs = new Abs();
  const NB = 1 << 24, tape = new Uint8Array(NB);
  let pos = NB >> 1, q = 0, lo = pos, hi = pos;
  let events = 0;
  for (let s = 0; s < maxSteps; s++) {
    const sym = tape[pos], t = rows[q][sym];
    if (!t) { console.log(`RAW HALT at ${s}`); process.exit(1); }
    const isD1 = q === 3 && sym === 1 && s >= 8;   // s5's D1 is inside startup
    tape[pos] = t.w; pos += t.d === 'R' ? 1 : -1; q = t.q;
    if (pos < lo) lo = pos; if (pos > hi) hi = pos;
    if (isD1) {
      const wall = [], right = [];
      for (let i = pos; i >= lo; i--) {
        const v = tape[i];
        if (wall.length && wall[wall.length - 1][0] === v) wall[wall.length - 1][1]++;
        else wall.push([v, 1]);
      }
      while (wall.length && wall[wall.length - 1][0] === 0) wall.pop();
      for (let i = pos + 1; i <= hi; i++) {
        const v = tape[i];
        if (right.length && right[right.length - 1][0] === v) right[right.length - 1][1]++;
        else right.push([v, 1]);
      }
      while (right.length && right[right.length - 1][0] === 0) right.pop();
      abs.nextCheckpoint();
      const rawSnap = JSON.stringify({ w: wall, r: right });
      if (abs.snap() !== rawSnap) {
        console.log(`DIVERGENCE at event ${events}, raw step ${s}`);
        console.log('  raw: ' + rawSnap);
        console.log('  abs: ' + abs.snap());
        process.exit(1);
      }
      events++;
    }
  }
  console.log(`co-verified ${events} excursion entries over ${maxSteps} raw steps: EXACT MATCH`);
  console.log(`  gap0=${abs.stats.gap0} fill=${abs.stats.fill} exits=${JSON.stringify(abs.stats.exits)}`);
}

const cls = (n) => (n <= 8 ? String(n) : n % 2 ? 'o' : 'e');
// Two-level RLE: collapse maximal exact repeats of adjacent run PAIRS into
// (v n v n)^k tokens, so (01)^P pair regions and (1100)^d lattices become
// single tokens; abstract lengths and repeat counts by cls afterwards.
function tok(runs) {
  const out = []; let i = 0;
  while (i < runs.length) {
    if (i + 3 < runs.length) {
      const [v1, n1] = runs[i], [v2, n2] = runs[i + 1];
      let k = 1;
      while (i + 2 * k + 1 < runs.length) {
        const [w1, m1] = runs[i + 2 * k], [w2, m2] = runs[i + 2 * k + 1];
        if (w1 === v1 && m1 === n1 && w2 === v2 && m2 === n2) k++; else break;
      }
      if (k >= 2) { out.push(`(${v1}${cls(n1)}${v2}${cls(n2)})^${cls(k)}`); i += 2 * k; continue; }
    }
    const [v, n] = runs[i]; out.push(`${v}${cls(n)}`); i++;
  }
  return out.join(' ');
}

// Wall abstraction at exactly the granularity the excursion transducer reads:
// per 1-run its parity (odd exits via f1A, even continues), per 0-run
// min(g,4) (1 degen, 2 cs-continue, 3 cs+bitset_odd, >=4 cs+bitset).
function wsig(runs) {
  const t = runs.map(([v, n]) => (v === 1 ? (n % 2 ? 'O' : 'E') : String(Math.min(n, 4))));
  const out = []; let i = 0;
  while (i < t.length) {
    if (i + 3 < t.length && !t[i].startsWith('(')) {
      let k = 1;
      while (i + 2 * k + 1 < t.length && t[i + 2 * k] === t[i] && t[i + 2 * k + 1] === t[i + 1]) k++;
      if (k >= 2) { out.push(`(${t[i]}${t[i + 1]})^${cls(k)}`); i += 2 * k; continue; }
    }
    out.push(t[i]); i++;
  }
  return out.join(' ');
}

function runMine(maxEvents) {
  const abs = new Abs();
  const seen = new Map(), seenW = new Map(), seenR = new Map();
  const CAP = 500000;
  let maxWall = 0, maxRight = 0;
  const growth = [];
  try {
    while (abs.stats.events < maxEvents) {
      abs.nextCheckpoint();
      const kw = wsig(abs.wall), kr = tok(abs.right);
      const k = kw + ' | ' + kr;
      seen.set(k, (seen.get(k) ?? 0) + 1);
      seenW.set(kw, (seenW.get(kw) ?? 0) + 1);
      seenR.set(kr, (seenR.get(kr) ?? 0) + 1);
      if (abs.wall.length > maxWall) maxWall = abs.wall.length;
      if (abs.right.length > maxRight) maxRight = abs.right.length;
      if (abs.stats.events % 250000 === 0)
        growth.push(`${abs.stats.events}: joint=${seen.size} wall=${seenW.size} right=${seenR.size}`);
      if (seen.size > CAP) throw new Error(`signature blowup: >${CAP} distinct`);
    }
  } catch (e) {
    console.log('STOPPED: ' + e.message);
  }
  console.log(`events=${abs.stats.events} gap0=${abs.stats.gap0} fill=${abs.stats.fill}`);
  console.log(`distinct: joint=${seen.size} wall=${seenW.size} right=${seenR.size}`);
  console.log('growth: ' + growth.join(' | '));
  console.log(`max run-count: wall=${maxWall} right=${maxRight}`);
  console.log(`exits=${JSON.stringify(abs.stats.exits)}`);
  for (const [label, m] of [['wall', seenW], ['right', seenR]]) {
    const sorted = [...m.entries()].sort((a, b) => b[1] - a[1]);
    console.log(`\ntop ${label} shapes:`);
    for (const [k, v] of sorted.slice(0, 25)) console.log(`  ${String(v).padStart(9)}  ${k}`);
    console.log(`rarest ${label} shapes:`);
    for (const [k, v] of sorted.slice(-10)) console.log(`  ${String(v).padStart(9)}  ${k}`);
  }
}

function runDump(count) {
  const abs = new Abs();
  for (let i = 0; i < count; i++) {
    abs.nextCheckpoint();
    console.log(`${String(i).padStart(3)}  ${wsig(abs.wall)} | ${tok(abs.right)}`);
  }
}

// The fill-safety walk: at a CE-fill (right = 1^c 0^inf, wall top popped by
// one), the exposed solid run's fate is decided by the wall runs alone.
// u = usable 1s on top. u=0 exposes a (0,.)/P1 exit that erases the odd run:
// DEATH. u odd: the run ends (1,0): f1A absorbs the run into the wall: SAFE.
// u=2: one carry caps, then cs re-exposes: g=1 degen-erases the (even)
// capped run: SAFE; g=2: cs descends into the next slot run: RECURSE;
// g>=3: cs then (0,.)/P1 erases the re-exposed odd run: DEATH.
// u>=4 even: two carries insulate the frozen even run behind 01-pairs: SAFE.
function fillWalk(wall) {
  let i = 0;
  let u = (wall[0]?.[0] === 1 ? wall[0][1] : 0) - 1;   // top run minus the fill's pop
  let depth = 0;
  for (;;) {
    if (u <= 0) return { verdict: 'DEATH-exposed', depth };
    if (u % 2 === 1) return { verdict: 'absorb', depth };
    if (u >= 4) return { verdict: 'insulate', depth };
    const g = wall[i + 1]?.[0] === 0 ? wall[i + 1][1] : Infinity;  // gap below
    if (g === 1) return { verdict: 'degen', depth };
    if (g >= 3) return { verdict: 'DEATH-uncap', depth };
    i += 2; depth++;
    u = wall[i]?.[0] === 1 ? wall[i][1] : 0;
  }
}

// Census the DANGEROUS moments: every CE with d >= 2 (a real fill). Record
// (c mod 4, right rest, walk verdict + depth, wall shape).
function runFills(maxEvents) {
  const abs = new Abs();
  const verdicts = new Map();
  const walls = new Map();
  let deaths = 0;
  abs.onCE = (c, d) => {
    if (d < 2) return;
    const wk = fillWalk(abs.wall);
    const rest = abs.right.length ? tok(abs.right) : '';
    const k = `c%4=${c % 4} rest=[${rest}] ${wk.verdict} depth=${wk.depth}`;
    verdicts.set(k, (verdicts.get(k) ?? 0) + 1);
    if (wk.verdict.startsWith('DEATH')) {
      deaths++;
      console.log(`DEATH VERDICT: c=${c} d=${d} wall=${JSON.stringify(abs.wall.slice(0, 8))}`);
    }
    const w = `${wk.verdict}: ${wsig(abs.wall)}`;
    walls.set(w, (walls.get(w) ?? 0) + 1);
  };
  try {
    while (abs.stats.events < maxEvents) abs.nextCheckpoint();
  } catch (e) { console.log('STOPPED: ' + e.message); }
  console.log(`events=${abs.stats.events} fills=${abs.stats.fill} deaths=${deaths}`);
  console.log('\nwalk verdicts:');
  for (const [k, v] of [...verdicts.entries()].sort((a, b) => b[1] - a[1]))
    console.log(`  ${String(v).padStart(7)}  ${k}`);
}

// Window census: the checkpoint signatures surrounding every fill, to read
// off the two enclosing composites (absorb / insulate) as exact statements.
function runWindows(maxEvents) {
  const abs = new Abs();
  const hist = [];          // ring of recent checkpoint signatures
  let pending = -1;         // countdown of post-fill checkpoints to capture
  const wins = new Map();
  let lastFillC = 0;
  abs.onCE = (c, d) => { if (d >= 2) { pending = 5; lastFillC = c; } };
  try {
    while (abs.stats.events < maxEvents) {
      abs.nextCheckpoint();
      const s = `${wsig(abs.wall)} § ${tok(abs.right)}`;
      hist.push(s); if (hist.length > 9) hist.shift();
      if (pending > 0) pending--;
      else if (pending === 0) {
        pending = -1;
        const k = `c%4=${lastFillC % 4}\n      ` + hist.join('\n      ');
        wins.set(k, (wins.get(k) ?? 0) + 1);
      }
    }
  } catch (e) { console.log('STOPPED: ' + e.message); }
  console.log(`events=${abs.stats.events} fills=${abs.stats.fill} distinct-windows=${wins.size}`);
  for (const [k, v] of [...wins.entries()].sort((a, b) => b[1] - a[1]).slice(0, 12))
    console.log(`\n  x${v}  ${k}`);
}

if (MODE === 'verify') runVerify(N);
else if (MODE === 'mine') runMine(N);
else if (MODE === 'fills') runFills(N);
else if (MODE === 'windows') runWindows(N);
else runDump(N);
