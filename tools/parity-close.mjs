// Closure model-checker for the parity machine's run-level invariant.
//
// Mirrors coq/Parity.v EXACTLY: exc / mstep transcribed literally (list form),
// plus an RLE twin for fast orbit replay. The candidate invariant invb is
// developed here first; only a JS-closed invariant gets encoded in Coq.
//
//   node parity-close.mjs --cross 200000     RLE mstep == list mstep on orbit
//   node parity-close.mjs --replay 30000000  orbit census: invb at every state
//   node parity-close.mjs --close            synthetic closure: Inv -> Inv
//   node parity-close.mjs --chunkstep 2000000  F-successor map, validated
//
// Wall lists are top-first arrays of 0/1 (Coq: list Sym, ws *> const 0).
// RLE walls are arrays of [sym, len], top-first. rs is an array of nats.

import { writeFileSync } from 'node:fs';

const args = process.argv.slice(2);
const MODE = args[0] ?? '--close';
const N = Number(args[1] ?? 2e6);

// ---------------------------------------------------------------- Coq mirror
// Fixpoint exc (ws : list Sym) (cap : bool) (rs : list nat) : xexit
function cpush(cap, rs) {
  if (cap) return [1, ...rs];
  if (rs.length === 0) return [1];
  return [rs[0] + 1, ...rs.slice(1)];
}
function push3(rs) {
  if (rs.length === 0) return [3];
  return [rs[0] + 3, ...rs.slice(1)];
}
function excL(ws, cap, rs) {
  for (let i = 0; ; ) {
    const a = ws[i], b = ws[i + 1];
    if (a === 1 && b === 1) { rs = cpush(cap, rs); cap = true; i += 2; continue; }
    if (a === 1 && b === 0) return { t: 'B', ws: [1, ...ws.slice(i + 2)], rs: cpush(cap, rs) };
    if (a === 1 && b === undefined) return { t: 'B', ws: [1], rs: cpush(cap, rs) };
    if (a === 0 && b === 0) {
      if (cap) { rs = push3(rs); cap = false; i += 2; continue; }
      return { t: 'C', ws: [1, 1, ...ws.slice(i + 2)], rs };
    }
    if (a === 0 && b === 1) {
      return { t: 'C', ws: cap ? [1, 1, 1, ...ws.slice(i + 2)] : [1, 1, ...ws.slice(i + 2)], rs };
    }
    // a = 0, b = undefined  |  ws empty
    const tail = rs2 => ({ t: 'C', ws: [1, 1], rs: rs2 });
    if (a === 0 || a === undefined) return cap ? tail(push3(rs)) : tail(rs);
    throw new Error('excL: bad cell');
  }
}
// Definition mstep (s : mst) : option mst
function mstepL(s) {
  const { m, ws, rs } = s;
  if (m === 'B') {
    if (rs.length === 0) return null;
    const [a, ...rest] = rs;
    return { m: 'C', ws: [...Array(a + 1).fill(1), ...ws], rs: rest };
  }
  if (rs.length === 0) {
    if (ws[0] !== 1) return null;
    const x = excL(ws.slice(1), false, [3]);
    return { m: x.t, ws: x.ws, rs: x.rs };
  }
  if (rs.length === 1) {
    if (rs[0] % 2 !== 0) return null;
    if (ws[0] !== 1) return null;
    const x = excL(ws.slice(1), false, [3 + rs[0]]);
    return { m: x.t, ws: x.ws, rs: x.rs };
  }
  const x = excL([...Array(rs[0] + 1).fill(0), ...ws], false, rs.slice(1));
  return { m: x.t, ws: x.ws, rs: x.rs };
}

// ------------------------------------------------------------------ RLE twin
// wall = [[sym,len],...] top-first, normalized (alternating, lens >= 1).
function rpop(wall, k) {           // pop k cells off the top, in place
  while (k > 0 && wall.length) {
    const t = wall[0], take = Math.min(k, t[1]);
    t[1] -= take; k -= take;
    if (t[1] === 0) wall.shift();
  }
}
function rpush(wall, sym, len) {
  if (len <= 0) return;
  if (wall.length && wall[0][0] === sym) wall[0][1] += len;
  else wall.unshift([sym, len]);
}
function wcellR(wall, i) { for (const [v, n] of wall) { if (i < n) return v; i -= n; } return undefined; }
// exc on RLE wall (consumes wall in place; returns exit)
function excR(wall, cap, rs) {
  for (;;) {
    const a = wcellR(wall, 0), b = wcellR(wall, 1);
    if (a === 1 && b === 1) {
      // consume 1-pairs in bulk: run of length L contributes floor(L/2) carries
      const L = wall[0][1];
      const pairs = Math.floor(L / 2);
      const wholeRun = wall.length === 1 || wall[1][0] === 0 || true; // runs alternate; next is 0-run or end
      // careful: if L is even, after pairs the next dispatch sees (next run); if odd, sees (1, next)
      rpop(wall, pairs * 2);
      if (pairs > 0) {
        rs = cpush(cap, rs); cap = true;
        for (let i = 1; i < pairs; i++) rs = cpush(true, rs);
      }
      continue;
    }
    if (a === 1 && (b === 0 || b === undefined)) {
      rpop(wall, 2);              // the 1 and the 0 (0 may be virtual blank)
      rpush(wall, 1, 1);
      return { t: 'B', rs: cpush(cap, rs) };
    }
    if (a === 0 && b === 0) {
      if (cap) { rpop(wall, 2); rs = push3(rs); cap = false; continue; }
      rpop(wall, 2);
      rpush(wall, 1, 2);
      return { t: 'C', rs };
    }
    if (a === 0 && b === 1) {
      rpop(wall, 2);
      rpush(wall, 1, cap ? 3 : 2);
      return { t: 'C', rs };
    }
    // a === 0/undefined at blank end
    if (a === 0 && b === undefined) rpop(wall, 1);
    wall.length = 0;
    rpush(wall, 1, 2);
    return { t: 'C', rs: cap ? push3(rs) : rs };
  }
}
function mstepR(s) {
  const { m, wall, rs } = s;
  if (m === 'B') {
    if (rs.length === 0) return null;
    const [a, ...rest] = rs;
    rpush(wall, 1, a + 1);
    return { m: 'C', wall, rs: rest };
  }
  if (rs.length <= 1) {
    if (rs.length === 1 && rs[0] % 2 !== 0) return null;
    if (wcellR(wall, 0) !== 1) return null;
    rpop(wall, 1);
    const x = excR(wall, false, [3 + (rs[0] ?? 0)]);
    return { m: x.t, wall, rs: x.rs };
  }
  rpush(wall, 0, rs[0] + 1);
  const x = excR(wall, false, rs.slice(1));
  return { m: x.t, wall, rs: x.rs };
}

// ------------------------------------------------------------- the invariant
const fillok = u => u >= 1 && (u % 4 === 0 || u % 4 === 1);
const m4ge4 = v => v >= 4 && v % 4 === 0;
const G = (T, g) =>
  !(T % 2 === 0 && g === 1) &&
  !((T === 2 || T === 6) && g === 2) &&
  !(T === 5 && g === 1);

// rs clauses. T = top run, below = wall RLE after the top run (starts with
// the gap 0-run or is empty). The stage scan simulates the decay: 1-heads
// pump T by 2, >=2-heads reset T to 2 and bury the old top; the final
// single's fill is checked with xsafe (class + gap guards + ladder).
let leafInfo = null;
function xcheck(w, u, L) {
  const fail = tag => {
    if (!leafInfo) leafInfo = { tag, w: w.map(r => [...r]), u, L };
    return tag;
  };
  if (u < 1 || u % 4 > 1) return fail('stage:fillok');
  const T = u + 1;
  const g = w.length && w[0][0] === 0 ? w[0][1] : 0;
  if (T % 2 === 0 && g === 1) return fail('stage:g1');
  if (T === 6 && g === 2) return fail('stage:g2');
  if (T === 5 && g === 1) return fail('stage:g5');
  if (T === 2 && g === 2) return fail('stage:g22');
  return xsafe(w, u, L);
}
function rsbad(rs, T, below) {
  if (rs.some(v => v < 1)) return 'run0';
  if (rs.length === 0) {
    if (T < 6 || T % 4 !== 2) return 'nil:T';    // nil states are born MB [a] -> T = a+2
    return xcheck(below, T - 1, 0);
  }
  for (const v of rs) if (v % 4 > 1) return 'val';   // values = 0 or 1 mod 4
  if (!m4ge4(rs[rs.length - 1])) return 'last';
  let Tc = T, w = below;
  for (let i = 0; i < rs.length - 1; i++) {
    if (rs[i] === 1) Tc = norm(Tc + 2);
    else { w = [[0, norm(rs[i] - 1)], [1, norm(Tc)], ...w]; Tc = 2; }
  }
  return xcheck(w, norm(Tc - 1), rs[rs.length - 1]);
}

// Wall clauses on RLE runs: 1-run top; interior 1-runs are never singletons
// (old wallok, validated); interior 0-runs (below the top gap) are >= 3
// (gap0 pushes are c-1 with c = 0,1 mod 4 and c >= 4).
const WALLCHECK = !process.argv.includes('nowall');
function wallbad(runs) {
  if (!runs.length || runs[0][0] !== 1) return 'top';
  if (!WALLCHECK) return null;
  for (let i = 1; i < runs.length; i++) {
    const [v, n] = runs[i];
    if (v === 1 && n < 2) return 'w1';
  }
  return null;
}

// ---------------------------------------------------------------- xsafe
// Class normalization: all guards use thresholds <= 6 plus mod-4 classes,
// so values/lengths are exact below 14 and collapse to 12+(v%4) above. This
// makes the ladder recursion's state space finite; cycles hit the memo.
const NORMCAP = Number(process.env.NORMCAP ?? 13);
const norm = v => (v <= NORMCAP ? v : (NORMCAP - 1 - ((NORMCAP - 1) % 4)) + (v % 4));
const normRuns = runs => runs.map(([s, n]) => [s, norm(n)]);
const normRs = rs => rs.map(norm);

// The fill excursion, walked with the rs stack tracked exactly: H (the
// merged entry head, generically 8 = 4+c, c = 0 mod 4) at the bottom and
// deep-generated values above. cpush(true) prepends a 1; cpush(false) and
// push3 mutate the head in place. Every exit state must satisfy the full
// invariant (invbad), recursing down the ladder. Memo + depth cap.
let xdepth = 0;
let xmemo = new Map();
function xsafe(runsBelow, u, L) {
  const nb = normRuns(runsBelow), nu = norm(u), nL = norm(L);
  const key = nu + ';' + nL + '|' + nb.map(r => r[0] + '.' + r[1]).join(',');
  const hit = xmemo.get(key);
  if (hit !== undefined) return hit === 'RUNNING' ? null : hit;
  if (xdepth > 300) return 'xdeep';
  xmemo.set(key, 'RUNNING');
  xdepth++;
  const r = xsafeRun(nb, nu, nL);
  xdepth--;
  xmemo.set(key, r);
  return r;
}
// Concrete: run the REAL excursion (excL) from the fill shape and check the
// exit state against the invariant; recursion happens through the exit's
// own stage scan. Norm keeps the key space finite; cycles read as safe.
function xsafeRun(runsBelow, u, L) {
  const wall = [...Array(u).fill(1)];
  for (const [v, n] of runsBelow) for (let i = 0; i < n; i++) wall.push(v);
  const x = excL(wall, false, [3 + L]);
  const runs = wallRunsOfList(x.ws);
  const bad = invbad(x.t, runs, normRs(x.rs));
  return bad && `x${x.t}[${bad}]`;
}

function wallRunsOfList(ws) {
  const runs = [];
  for (const c of ws) {
    if (runs.length && runs[runs.length - 1][0] === c) runs[runs.length - 1][1]++;
    else runs.push([c, 1]);
  }
  while (runs.length && runs[runs.length - 1][0] === 0) runs.pop();  // blank tail
  return runs;
}
const wallT = runs => (runs.length && runs[0][0] === 1 ? runs[0][1] : 0);
const wgapR = runs => (runs.length > 1 && runs[1][0] === 0 ? runs[1][1] : 0);
const ztl = runs => {               // zrun (tl ws) for a T=1 wall
  if (!runs.length || runs[0][0] !== 1) return NaN;
  if (runs[0][1] > 1) return 0;
  return runs.length > 1 && runs[1][0] === 0 ? runs[1][1] : 0;
};

// invb on (m, wall-runs, rs). Returns null (ok) or a violation tag.
function invbad(m, runs, rs) {
  const T = wallT(runs);
  const wb = wallbad(runs);
  if (wb) return `wall:${wb}`;
  const below = runs.slice(1);
  if (m === 'C') {
    if (T < 2) return 'C:T';
    const bad = rsbad(rs, T, below);
    return bad && `C:${bad}`;
  }
  if (T !== 1) return 'B:T';
  if (rs.length === 0) return 'B:nil';
  const [a, ...rest] = rs;
  if (a % 4 > 1) return 'B:val';
  const bad = rsbad(rest, a + 2, below);
  return bad && `B:${bad}`;
}

// ------------------------------------------------------------------- replay
const wallStr = (runs, k = 10) =>
  runs.slice(0, k).map(([v, n]) => `${v}^${n}`).join(' ') + (runs.length > k ? ' ..' : '');
const rsStr = (rs, k = 10) => rs.slice(0, k).join(',') + (rs.length > k ? ',..' : '');

function replay(maxEvents) {
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  const viol = new Map();
  const fillU = new Map();
  const valPos = new Map();         // where do values other than 1 / 4N sit
  const region = new Map();         // interior 1-run mod4 census (reachable region)
  let maxDepth = 0;
  for (let ev = 0; ev < maxEvents; ev++) {
    const runs = s.wall;
    leafInfo = null;
    const bad = invbad(s.m, runs, s.rs);
    if (bad) {
      if (!viol.has(bad)) viol.set(bad, { n: 0, ex: [] });
      const v = viol.get(bad);
      v.n++;
      if (v.ex.length < 5) {
        v.ex.push(`${s.m} [${wallStr(runs)}] rs=[${rsStr(s.rs)}]`);
        if (leafInfo) v.ex.push(`   LEAF ${leafInfo.tag}: u=${leafInfo.u} L=${leafInfo.L} w=[${wallStr(leafInfo.w)}]`);
      }
    }
    s.rs.forEach((v, i) => {
      if (v !== 1 && v % 4 !== 0) {
        const pos = i === 0 ? 'head' : i === s.rs.length - 1 ? 'last' : 'mid';
        const k = `${s.m}:${pos} v%4=${v % 4}${v <= 13 ? ' v=' + v : ''}`;
        valPos.set(k, (valPos.get(k) ?? 0) + 1);
      }
    });
    {
      let i = 1;
      if (i < runs.length && runs[i][0] === 0 && runs[i][1] % 2 === 0) {
        for (i++; i < runs.length; i++) {
          const [v, n] = runs[i];
          if (v === 0) { if (n % 2 === 1) break; continue; }
          const k = `run%4=${n % 4}${n <= 9 ? ' n=' + n : ''}`;
          region.set(k, (region.get(k) ?? 0) + 1);
        }
      }
    }
    if (s.m === 'C' && s.rs.length <= 1) {
      const u = wallT(runs) - 1, g = wgapR(runs);
      const k = `u%4=${u % 4}${u <= 13 ? ' u=' + u : ''} g=${g > 3 ? 'big' : g}`;
      fillU.set(k, (fillU.get(k) ?? 0) + 1);
    }
    const before = s.wall.reduce((n, [, l]) => n + l, 0);
    const next = mstepR(s);
    if (!next) { console.log(`STUCK at event ${ev}: ${s.m} rs=[${s.rs}]`); break; }
    if (s.m === 'C') {
      const after = next.wall.reduce((n, [, l]) => n + l, 0);
      maxDepth = Math.max(maxDepth, before - after + 3);
    }
    s = next;
  }
  console.log(`replayed; final wall cells=${s.wall.reduce((n, [, l]) => n + l, 0)}; max depth ~ ${maxDepth}`);
  console.log('--- violations:', viol.size ? '' : 'NONE');
  for (const [tag, v] of viol) {
    console.log(`  ${v.n}x ${tag}`);
    for (const e of v.ex) console.log(`     ${e}`);
  }
  console.log('--- fill (u mod 4, g) census:');
  for (const [k, n] of [...fillU].sort((x, y) => y[1] - x[1]).slice(0, 20)) console.log(`  ${n}x ${k}`);
  console.log('--- rs values not in {1} u 4N, by position:');
  for (const [k, n] of [...valPos].sort((x, y) => y[1] - x[1]).slice(0, 20)) console.log(`  ${n}x ${k}`);
  console.log('--- reachable-region interior 1-runs:');
  for (const [k, n] of [...region].sort((x, y) => y[1] - x[1]).slice(0, 20)) console.log(`  ${n}x ${k}`);
}

// -------------------------------------------------------------- cross-check
function crossCheck(maxEvents) {
  let sl = { m: 'B', ws: [1], rs: [4] };
  let sr = { m: 'B', wall: [[1, 1]], rs: [4] };
  for (let ev = 0; ev < maxEvents; ev++) {
    const nl = mstepL(sl);
    const nr = mstepR({ m: sr.m, wall: sr.wall.map(r => [...r]), rs: sr.rs });
    if (!nl !== !nr) throw new Error(`cross: null mismatch at ${ev}`);
    if (!nl) { console.log('both stuck at', ev); return; }
    const rlist = [];
    for (const [v, n] of nr.wall) for (let i = 0; i < n; i++) rlist.push(v);
    const llist = [...nl.ws];
    while (llist.length && llist[llist.length - 1] === 0) llist.pop();
    while (rlist.length && rlist[rlist.length - 1] === 0) rlist.pop();
    if (nl.m !== nr.m || llist.join('') !== rlist.join('') || nl.rs.join(',') !== nr.rs.join(','))
      throw new Error(`cross: state mismatch at ${ev}\n  L: ${nl.m} ${llist.join('')} [${nl.rs}]\n  R: ${nr.m} ${rlist.join('')} [${nr.rs}]`);
    sl = nl; sr = nr;
  }
  console.log(`cross-check OK at ${maxEvents} events`);
}

// -------------------------------------------------------- synthetic closure
function* rsShapes() {
  const Q = [4, 8, 12];        // 0 mod 4 (legal lasts)
  const P = [5, 9];            // 1 mod 4 heads/mids
  const B = [...Q, ...P];      // legal >=2 values anywhere but last
  yield [];
  for (const L of Q) {
    for (let p = 0; p <= 5; p++) yield [...Array(p).fill(1), L];
    for (const b of B) {
      for (let m = 0; m <= 4; m++) {
        yield [b, ...Array(m).fill(1), L];
        for (let p = 1; p <= 3; p++) yield [...Array(p).fill(1), b, ...Array(m).fill(1), L];
        for (const b2 of [4, 5, 8]) for (let m2 = 0; m2 <= 2; m2++)
          yield [b2, ...Array(m2).fill(1), b, ...Array(m).fill(1), L];
      }
    }
  }
}
function* wallShapes() {
  // 1^T [0^g tail], tails = stacks of (1-run >= 2, 0-run) segments, optional
  // trailing bare 1-run. This overapproximates the reachable wall language.
  const tails = [[]];
  const seg1 = [2, 3, 4, 5, 9];
  const seg0 = [1, 2, 3, 4, 7];
  for (const n of seg1) tails.push([[1, n]]);
  for (const n of seg1) for (const f of seg0) tails.push([[1, n], [0, f], [1, 2]]);
  for (const n of [2, 3, 5]) for (const f of [1, 2, 3]) for (const n2 of [2, 7])
    tails.push([[1, n], [0, f], [1, n2], [0, 3], [1, 2]]);
  for (let T = 1; T <= 16; T++) {
    yield [[1, T]];
    for (const g of [1, 2, 3, 4, 5, 6, 7, 8]) {
      for (const tail of tails) {
        const runs = [[1, T], [0, g], ...tail.map(r => r.slice())];
        while (runs.length && runs[runs.length - 1][0] === 0) runs.pop();
        yield runs;
      }
    }
  }
}
function listOfRuns(runs) {
  const out = [];
  for (const [v, n] of runs) for (let i = 0; i < n; i++) out.push(v);
  return out;
}

function closeCheck() {
  const rss = [...rsShapes()];
  let states = 0, bad = 0;
  const viol = new Map();
  for (const runs of wallShapes()) {
    const ws = listOfRuns(runs);
    const T = wallT(runs);
    for (const rs of rss) {
      for (const m of ['C', 'B']) {
        if (invbad(m, runs, rs)) continue;      // not an Inv state
        states++;
        const next = mstepL({ m, ws, rs });
        if (!next) {
          bad++;
          if (!viol.has('NONE')) viol.set('NONE', []);
          const ex = viol.get('NONE');
          if (ex.length < 6) ex.push(`${m} [${wallStr(runs)}] rs=[${rsStr(rs)}]`);
          continue;
        }
        const nruns = wallRunsOfList(next.ws);
        const nb = invbad(next.m, nruns, next.rs);
        if (nb) {
          bad++;
          if (!viol.has(nb)) viol.set(nb, []);
          const ex = viol.get(nb);
          if (ex.length < 6)
            ex.push(`${m} [${wallStr(runs)}] rs=[${rsStr(rs)}]  ->  ${next.m} [${wallStr(nruns)}] rs=[${rsStr(next.rs)}]`);
        }
      }
    }
  }
  console.log(`closure: ${states} Inv states checked, ${bad} bad successors`);
  for (const [tag, exs] of viol) {
    console.log(`-- ${tag}:`);
    for (const e of exs) console.log('   ' + e);
  }
}

// ------------------------------------------------------------ F / chunkstep
// F-state predicate, matching --grammar exactly: MC, wall top run 1s of
// length 2 or 4, rs.length >= 2, rs[0] >= 4. Validated (--grammar) that
// every reachable such state parses below with zero failures.
function parseF(s) {
  if (!(s.m === 'C' && s.wall.length && s.wall[0][0] === 1
      && (s.wall[0][1] === 2 || s.wall[0][1] === 4)
      && s.rs.length >= 2 && s.rs[0] >= 4)) return null;
  if (s.wall.length % 2 === 0) return null;         // must end in a 1-run
  const top = s.wall[0][1];
  const stack = [];
  for (let i = 1; i < s.wall.length; i += 2) {
    if (s.wall[i][0] !== 0 || !s.wall[i + 1] || s.wall[i + 1][0] !== 1) return null;
    stack.push([s.wall[i][1], s.wall[i + 1][1]]);
  }
  const rs = s.rs;
  const H = rs[0], L = rs[rs.length - 1];
  let p = 0, i = rs.length - 2;
  while (i >= 1 && rs[i] === 1) { p++; i--; }
  const W = rs.slice(1, i + 1);
  if (!W.every(v => v === 1 || v === 5 || v === 9)) return null;
  if (L % 4 !== 0 || L < 4) return null;
  if (!(H === 4 || H === 5 || H === 9 || (H % 4 === 0 && H >= 8))) return null;
  return { top, stack, H, W, p, L };
}

// chunkstep(F): the boundary-to-boundary successor map, a pure function of
// parseF's output. Two phases, matching the abstract machine's own split
// (mstep's rs.length>=2 branch vs its rs.length<=1 excursion branch):
//
// Phase 1 walks the rs prefix [H, ...W] left to right. Every mstep call
// with rs.length>=2 is UNIFORM regardless of the popped value v (proof:
// pushing 0^(v+1) always makes the excursion's first two cells 0,0 with
// cap=false, which exits immediately): it buries the current run under a
// fresh top-2 with a gap of v-1 below it, OR -- when v=1 -- just grows the
// current run by 2 (the pushed 0,0 cancels against the immediate C-exit
// merge). So each non-1 symbol closes an entry (gap=v-1, run=<whatever the
// run had grown to>) and each 1 grows the run 2 at a time. The walk can
// land EXACTLY on a new boundary mid-prefix: as soon as a run has just
// become 2 or 4 (fresh close, or one grown step past it) and the next
// unconsumed symbol is itself >= 4, that IS the next F-state (verified
// against real W-nonempty transitions: this is the whole story for them --
// H/p/L are otherwise untouched).
//
// Phase 2 fires when the prefix is exhausted onto blank p ones then L
// (rs.length finally drops to 1): a real excursion, closing form derived
// and cross-checked against an oracle replaying the true orbit (see
// notes/parity.md, "The chunkstep successor map"). One p-lap always costs
// p -= 2, L += 8; a "double lap" is exactly two of those composed.
function chunkstep(F) {
  let accum = F.top;
  const entries = [];
  const seq = [F.H, ...F.W];
  for (let i = 0; i < seq.length; i++) {
    const v = seq[i];
    if (v === 1) accum += 2;
    else { entries.push([v - 1, accum]); accum = 2; }
    const next = seq[i + 1];
    if ((accum === 2 || accum === 4) && next !== undefined && next >= 4) {
      return {
        case: `phase1:closed=${entries.length}`,
        F: {
          top: accum, H: next, W: seq.slice(i + 2), p: F.p, L: F.L,
          stack: [...entries.slice().reverse(), ...F.stack],
        },
      };
    }
  }
  if (F.p === 0) return epoch(F);
  const preStack = [...entries.slice().reverse(), ...F.stack];
  return phase2(preStack, F.p, F.L);
}

function mk(caseKey, partial) {
  return { case: caseKey, F: { W: [], ...partial } };
}

// Shift the gap of the shallowest entry in a stack list by `delta`, leaving
// its run and everything deeper untouched. Used by every rule whose
// "next entry" gets nudged by a fixed amount.
function shiftFirst(entries, delta) {
  if (!entries.length) return entries;
  return [[entries[0][0] - delta, entries[0][1]], ...entries.slice(1)];
}

// F.p === 2 going into a double-lap rule (A:g3/A:g4/A:g2odd, k = 0): the
// lap's own p -= 4 would go negative. Oracle-verified (c1-sweep-p2.mjs) at
// this EXACT underflow depth: the excursion falls through to an epoch-like
// landing -- L' is a fixed constant (8) and p' = L/2 + 4 regardless of the
// entry or deeper stack; `entry` is the caller's already-fully-transformed
// [gap,run] (A:g3/A:g4 collapse gap to 1 with run shifted +1/+2 same as the
// non-underflow rule; A:g2odd leaves gap/run untouched, matching its own
// non-underflow rule -- only the deeper shift-by-1, applied by the caller
// before calling this, is shared). Two real 10M-orbit instances match
// exactly (ev7212 A:g3, ev471436 A:g2odd); k > 0 is untested (k does not
// affect the non-underflow p/L either, so assumed to not matter here, but
// not oracle-checked).
function p2Underflow(L, entry, tail, src) {
  return mk(`${src}-p2underflow`, { top: 2, H: 4, p: L / 2 + 4, L: 8, stack: [entry, ...tail] });
}

// True for the table-A/B sub-rules that leave the excursion still "mid
// flight": H is a generic placeholder (not a freshly-assigned digit or
// cascade value) and the real information is the transformed stack[0].
// digitBirth2's nestedGap1/nestedExcess also belong here -- their H=4 (or
// 4+4j) is the SAME kind of placeholder, confirmed by oracle
// (D:recurse:digitBirth2:nestedGap1 in the real 10M orbit stays table-D
// shape rather than being adopted). Used by table D's rest0-in-{3,4}
// recursion to decide adopt vs. stay.
function isContinuation(caseKey) {
  return /^(A:g3|A:g4|A:g2odd|B:g3|B:g4|B:g2odd)$/.test(caseKey)
    || /:nestedGap1$|:nestedExcess-UNVERIFIED$/.test(caseKey);
}

// The excursion's very first contact is with preStack[0] -- the entry
// Phase 1 just closed, gap = (last symbol it consumed) - 1, run = whatever
// the fresh run had grown to. If that gap is already >= 6 the contact is
// clean and preStack[1:] is untouched (oracle-confirmed with H in {8,9,12,
// 16}, any p >= 2, any top, any deeper stack): this alone is chunkBig
// (coq/Parity.v) generalized from H = 4c+8 to H = 9 too.
//
// If preStack[0]'s gap is small (3 or 4 -- H = 4 or H = 5; nothing else is
// possible, since every other H gives gap >= 7), preStack[0] is consumed
// as part of the SAME contact that resolves preStack[1] (or blank): the
// two-entry pair (preStack[0], preStack[1]) determines the outcome, not
// preStack[0] alone, and the pair's behavior depends on preStack[0].run
// too (= F.top), not just its gap. Four such pairs are possible (H in
// {4,5} x top in {2,4}); tables A/C are densely oracle-verified (many
// (gap,run) shapes, sentinel-checked for passivity beyond the touched
// entries), tables B/D rest on 2-3 confirmed points each and are flagged.
// Whenever F.W is non-empty going into a chunkstep call, Phase 1
// necessarily walked past it (W's symbols are only 5/9, so preStack[0] is
// always (4,accumulated) -- tableCGeneric -- or (8,accumulated) --
// chunkBig): a "9"-closure (chunkBig, gap=8) is a genuine fresh reset and
// clears W; a "5"-closure with an accumulated run (tableCGeneric, gap=4)
// reconstructs its OWN W directly from r0 (see there) rather than
// depending on F.W at all -- so phase2 itself never needs F.W as input.
// tableA/B/C/D can never see g0 from anything but H directly (their r0 in
// {2,4} is only reachable that way, which requires F.W empty).
function phase2(preStack, p, L) {
  const [g0, r0] = preStack[0];
  const rest = preStack.slice(1);
  if (g0 >= 6) {
    return mk('chunkBig', { top: 2, H: 4, p: p - 2, L: L + 8, stack: [[g0 - 5, r0], ...rest] });
  }
  if (g0 === 3 && r0 === 2) return tableA(rest, p, L);
  if (g0 === 4 && r0 === 2) return tableC(rest, p, L);
  if (g0 === 3 && r0 === 4) return tableB(rest, p, L);
  if (g0 === 4 && r0 === 4) return tableD(rest, p, L);
  // gap=3 only ever arises from H=4 itself (entries[0], run = F.top), so
  // r0 in {2,4} is exhaustive there. gap=4 can ALSO arise from a digit-5
  // Phase-1 closure with an accumulated (not F.top) run.
  if (g0 === 4) return tableCGeneric(r0, rest, p, L);
  throw new Error(`phase2: unexpected preStack[0]=(${g0},${r0})`);
}

// gap=4 reached via a digit-5 Phase-1 closure with an ACCUMULATED run (not
// F.top in {2,4}, i.e. r0 >= 6). The entry is a free absorb, and the
// excursion re-enters exactly the TOP-LEVEL dispatch on rest[0] (recursing
// through phase2 itself: rest here is already in preStack form,
// [[gap,run],...]). Whatever lap that sub-dispatch computes gets scaled by
// exactly 4x -- every table-A/chunkBig shape reachable from
// rest[0]=(H-1,F.top) checked (single lap -> quadruple, double lap ->
// octuple, table C's triple lap -> x4); shape (top,H,stack) passes through
// unchanged, only p/L scale (c1w-sweep-shift1x.mjs).
// W is NOT simply F.W passed through: r0's own accumulated closure is
// EXACTLY the [1 x (r0-2)/2, 5] word (reconstructed from r0 alone, not
// threaded in) -- when F.W held MORE than that (an embedded digit-9 from
// an earlier tableCGeneric hop), the earlier part was already consumed
// into rest[0]/rest[1]/... by Phase 1's OWN walk and is NOT part of this
// call's W at all; only the trailing segment that closed INTO r0 is. The
// sub-dispatch's own W (normally empty, but not always -- chunkBig never
// touches it, but a table-A digitBirth2/smallGap1 landing can) comes
// FIRST, this reconstructed word SECOND (oracle-verified against every
// real 10M-orbit instance with an embedded 9, e.g. ev2481292/ev2657934).
function tableCGeneric(r0, rest, p, L) {
  const sub = phase2(rest, p, L);
  // isContinuation(sub.case) breaks the naive 4x-scaled "adopt" below: it
  // either underflows p, or (even when it doesn't) wrongly treats a
  // mid-excursion continuation as a fresh landing. Both real 10M-orbit
  // occurrences (ev7551768: A:g3 sub exactly at p=8; ev8351703:
  // digitBirth2:nestedGap1 sub with the gap1-partner's run=2 AND a leading
  // (2,2) before it, j>=1) verified by direct oracle sweep
  // (c1-sweep-cgeneric*.mjs) and re-derived from `rest` directly -- NOT
  // from `sub`, whose own stack/H/W already fold the shape these formulas
  // need unfolded. j===0 (no leading (2,2)) is a DIFFERENT shape -- the old
  // naive formula below is actually correct there (oracle-confirmed against
  // ev2275572, a second real 10M instance: j=0 falls through on purpose).
  // Any other isContinuation shape (or either of these two at an unchecked
  // p) also falls through to the old formula.
  if (sub.case === 'A:g3' && p === 8 && rest[1]) {
    const k = (r0 - 2) / 2;
    return mk('C:shift1-EXTRAPOLATED:continuation-Ag3-p8', {
      top: 2, H: 4, W: [...Array(k - 1).fill(1), 5], p: L / 2 + 16, L: 8,
      stack: [[rest[1][0], rest[1][1] + 1], ...rest.slice(2)],
    });
  }
  if (/:nestedGap1$/.test(sub.case) && rest[0] && rest[0][0] === 3 && rest[0][1] === 2
      && rest[1] && rest[1][0] === 2 && rest[1][1] % 2 === 0 && rest[1][1] >= 4) {
    const trigR = rest[1][1];
    let j = 0;
    while (rest[2 + j] && rest[2 + j][0] === 2 && rest[2 + j][1] === 2) j++;
    const gp1 = rest[2 + j];
    if (j >= 1 && gp1 && gp1[0] === 1 && gp1[1] === 2) {
      const spacer = Array((trigR - 4) / 2).fill(1);
      const kOnes = Array((r0 - 2) / 2).fill(1);
      return mk('C:shift1-EXTRAPOLATED:continuation-nestedGap1', {
        top: 4, H: 5, W: [...spacer, 9, ...kOnes, 5], p: p - 8, L: L + 32,
        stack: rest.slice(2 + j + 1),
      });
    }
  }
  const dp = p - sub.F.p, dL = sub.F.L - L;
  const digitW = [...Array((r0 - 2) / 2).fill(1), 5];
  return {
    case: 'C:shift1-EXTRAPOLATED',
    F: { ...sub.F, W: [...sub.F.W, ...digitW], p: p - 4 * dp, L: L + 4 * dL },
  };
}

// H = 4, F.top = 2 (preStack[0] = (3,2), already spent in the contact).
// A run of leading (2,2) entries is the chunkCascade/chunkTerm k from
// coq/Parity.v: absorbed for free (no extra p-lap), landing on either
// blank (chunkTerm) or a gap>=6 entry (chunkCascade), H' = 4k+8 both ways.
// Reaching a >=6 gap WITHOUT any (2,2)'s first (k=0, straight from the
// (3,2) contact) shifts it by -4, one less than chunkBig's -5 since the
// (3,2) contact itself already spent one unit of gap.
function tableA(rest, p, L) {
  let k = 0;
  while (k < rest.length && rest[k][0] === 2 && rest[k][1] === 2) k++;
  const tail = rest.slice(k + 1);
  if (k >= rest.length) {
    return mk('A:chunkTerm', { top: 2, H: 4 * k + 8, p: p - 2, L: L + 8, stack: [] });
  }
  const [g, r] = rest[k];
  if (g >= 6) {
    return mk(k > 0 ? 'A:chunkCascade' : 'A:cleanK0', { top: 2, H: 4 * k + 8, p: p - 2, L: L + 8, stack: [[g - 4, r], ...tail] });
  }
  if (g === 3 && r === 3) return mk('A:g3term', { top: 4, H: 4 * k + 8, p: p - 2, L: L + 8, stack: tail });
  if (g === 4 && r === 2) return mk('A:g4term', { top: 4, H: 4 * k + 8, p: p - 2, L: L + 8, stack: tail });
  if (g === 3) {
    if (p === 2) return p2Underflow(L, [1, r + 1], tail, 'A:g3');
    return mk('A:g3', { top: 2, H: 4, p: p - 4, L: L + 16, stack: [[2 + 4 * k, r + 1], ...tail] });
  }
  if (g === 4) {
    if (p === 2) return p2Underflow(L, [1, r + 2], tail, 'A:g4');
    return mk('A:g4', { top: 2, H: 4, p: p - 4, L: L + 16, stack: [[2 + 4 * k, r + 1], ...tail] });
  }
  if (g === 5) return mk('A:g5', { top: 2, H: 4 * k + 8, p: p - 2, L: L + 8, stack: [[1, r], ...tail] });
  if (g === 2 && r % 2 === 1) {
    const shifted = tail.length ? [[tail[0][0] - 1, tail[0][1]], ...tail.slice(1)] : tail;
    if (p === 2) return p2Underflow(L, [2, r], shifted, 'A:g2odd');
    return mk('A:g2odd', { top: 2, H: 4, p: p - 4, L: L + 16, stack: [[3 + 4 * k, r], ...shifted] });
  }
  if (g === 2) return digitBirth2(r, tail, p, L, k);
  if (g === 1) return smallGap1(r, tail, p, L, k);
  throw new Error(`tableA: unhandled entry gap=${g} run=${r} k=${k}`);
}

// H = 5, F.top = 2 (preStack[0] = (4,2)). Oracle-confirmed uniform across
// blank, gap in {3,5,7} (i.e. independent of what preStack[1] is, unlike
// every other table): the contact always resolves to top'=4, H'=4, one
// p-lap and a half again (p -= 6, L += 24), shifting preStack[1]'s gap by
// -1 (run unchanged) if it exists. Deeper entries (preStack[2:]) are
// assumed passive by analogy with every other table; not independently
// oracle-checked with a sentinel beyond preStack[1].
function tableC(rest, p, L) {
  if (rest.length === 0) return mk('C:blank', { top: 4, H: 4, p: p - 6, L: L + 24, stack: [] });
  const [g, r] = rest[0];
  return mk('C:shift1', { top: 4, H: 4, p: p - 6, L: L + 24, stack: [[g - 1, r], ...rest.slice(1)] });
}

// H = 4, F.top = 4 (preStack[0] = (3,4)). Dense oracle sweep
// (c1w-sweep-BD2.mjs): a leading (2,2)-chain (j entries) is absorbed into
// H exactly like table A's (H' = 4+4j); past that, rest[0]'s gap selects a
// sub-rule. UNLIKE table D, the (3,4) contact's own cost is ALWAYS a
// single base lap (p -= 2, L += 8) -- never scaled by j or by anything
// past it -- and gap=1 is an EXACT match to table A's own smallGap1 with
// run shifted +2 (same W word, same lap, same deeper shift, verified
// r=2..9): reused directly rather than re-encoded.
function tableB(rest, p, L) {
  let j = 0;
  while (j < rest.length && rest[j][0] === 2 && rest[j][1] === 2) j++;
  const baseH = 4 + 4 * j;
  const tail = rest.slice(j);
  const P = p - 2, L2 = L + 8;
  if (tail.length === 0) return mk('B:blank', { top: 2, H: baseH, W: [5], p: P, L: L2, stack: [] });
  const [g, r] = tail[0];
  const after = tail.slice(1);
  if (g >= 5) return mk('B:big', { top: 2, H: baseH, W: [5], p: P, L: L2, stack: [[g - 4, r], ...after] });
  if (g === 1) return smallGap1(r + 2, after, p, L, 0);
  if (g === 3 && r === 3) return mk('B:g3term', { top: 4, H: baseH, W: [5], p: P, L: L2, stack: after });
  if (g === 4 && r === 2) return mk('B:g4term', { top: 4, H: baseH, W: [5], p: P, L: L2, stack: after });
  if (g === 2 && r % 2 === 0) return tableBEvenBirth(j, r, after, p, L);
  if (g === 2) return mk('B:g2odd', { top: 2, H: 5, p: P, L: L2, stack: [[4 + 4 * j, r], ...shiftFirst(after, 1)] });
  if (g === 3) return mk('B:g3', { top: 2, H: 5, p: P, L: L2, stack: [[3 + 4 * j, r + 1], ...after] });
  return mk('B:g4', { top: 2, H: 5, p: P, L: L2, stack: [[3 + 4 * j, r + 2], ...after] });
}

// A run of consecutive gap=2 even-run(>=4) entries after the (3,4) contact
// all birth digit 5 together: same deepest-first construction as
// digitBirth2's own even-chain (each level contributes floor((run-4)/2)
// ones then a symbol), but EVERY level uses '5' -- there is no outer '9'
// here, table B's own base birth is a genuinely separate extra '5'
// appended last (oracle: c1w-sweep-BD2.mjs gap=2 run=2..9, r=4/6/8 all
// land here with 0/1/2 leading ones plus the trailing base 5).
// tableBEvenBirth's evenChain closure for the ONE shape every real
// 10M-orbit "gap < 5 after the chain" instance has: a single-level chain
// (run r >= 8, no extension) with one leading AND one trailing (2,2)
// (j = j2 = 1). Oracle-derived (c1-sweep-tableB-even.mjs). The chain's own
// outer entry becomes [4+4j, r-2] (mirrors digitBirth2's r2>=8 "extra
// entry" regime one level up: table B's promoted digit is always '5', never
// '9') and sits ahead of beyond's own transform; term shapes fold BOTH
// entries into W instead (H'=4+4j, stack consumed).
function tableBEvenNested(j, r, g, run, tail, p, L) {
  const P = p - 2, L2 = L + 8;
  const baseH = 4 + 4 * j;
  if ((g === 3 && run === 3) || (g === 4 && run === 2)) {
    const spacer = Array((r - 4) / 2).fill(1);
    return mk('B:evenChain:nested', { top: 4, H: baseH, W: [...spacer, 9, 5], p: P, L: L2, stack: tail });
  }
  const outer = [baseH, r - 2];
  if (g === 1) return mk('B:evenChain:nested', { top: 2, H: 5, W: [], p: P, L: L2, stack: [outer, [4, run + 2], ...tail] });
  if (g === 2 && run % 2 === 1) return mk('B:evenChain:nested', { top: 2, H: 5, W: [], p: P, L: L2, stack: [outer, [8, run], ...shiftFirst(tail, 1)] });
  if (g === 3) return mk('B:evenChain:nested', { top: 2, H: 5, W: [], p: P, L: L2, stack: [outer, [7, run + 1], ...tail] });
  if (g === 4) return mk('B:evenChain:nested', { top: 2, H: 5, W: [], p: P, L: L2, stack: [outer, [7, run + 2], ...tail] });
  return null;
}

// j = a LEADING (2,2)-run already absorbed by tableB's own chain-scan
// before reaching this birth: mirrors digitBirth2's own fix -- it does NOT
// add 4j to H, it instead promotes the FIRST run's symbol to '9' (as if an
// outer digit-9-style trigger were present); a TRAILING (2,2)-run right
// after the whole even-run chain absorbs for free into H as usual (oracle:
// the real (2,2)(2,8)(...) instances).
function tableBEvenBirth(j, r, after, p, L) {
  const runs = [r];
  let idx = 0;
  while (idx < after.length && after[idx][0] === 2 && after[idx][1] % 2 === 0 && after[idx][1] >= 4) {
    runs.push(after[idx][1]); idx++;
  }
  let j2 = 0;
  while (idx + j2 < after.length && after[idx + j2][0] === 2 && after[idx + j2][1] === 2) j2++;
  const beyond = after.slice(idx + j2);
  const chainH = 4 + 4 * j2;
  const w = [];
  runs.forEach((rr, i) => {
    for (let n = 0; n < (rr - 4) / 2; n++) w.push(1);
    w.push((j > 0 && i === 0) ? 9 : 5);
  });
  w.push(5);
  const P = p - 2, L2 = L + 8;
  if (beyond.length === 0) return mk('B:evenChain:term', { top: 2, H: chainH, W: w, p: P, L: L2, stack: [] });
  const [g, r2] = beyond[0];
  if (g >= 5) return mk('B:evenChain:cascade', { top: 2, H: chainH, W: w, p: P, L: L2, stack: [[g - 4, r2], ...beyond.slice(1)] });
  // gap < 5: every real 10M-orbit instance (3x) has a single-level chain
  // (runs = [8]) with exactly one leading AND one trailing (2,2) (j = j2 =
  // 1). See tableBEvenNested for the oracle-derived closure over beyond.
  if (runs.length === 1 && runs[0] >= 8 && j2 === 1) {
    const hit = tableBEvenNested(j, runs[0], g, r2, beyond.slice(1), p, L);
    if (hit) return hit;
  }
  return mk('B:evenChain:nested-UNVERIFIED', { top: 2, H: chainH, W: w, p: P, L: L2, stack: beyond });
}

// H = 5, F.top = 4 (preStack[0] = (4,4)). Dense oracle sweep
// (c1w-sweep-BD2.mjs): the (4,4) contact ALWAYS costs exactly one base lap
// (p -= 8, L += 32) -- NEVER scaled, regardless of what rest holds; only
// the SHAPE varies with rest[0]'s gap.
function tableD(rest, p, L) {
  const P = p - 8, L2 = L + 32;
  if (rest.length === 0) return mk('D:blank', { top: 2, H: 4, W: [1, 5], p: P, L: L2, stack: [] });
  const [g, r] = rest[0];
  const after = rest.slice(1);
  if (g >= 6) return mk('D:big', { top: 2, H: 4, W: [1, 5], p: P, L: L2, stack: [[g - 5, r], ...after] });
  if (g === 5) {
    if (r === 2) return mk('D:g5term', { top: 4, H: 4, W: [1, 5], p: P, L: L2, stack: after });
    return mk('D:g5', { top: 4, H: 5, p: P, L: L2, stack: [[3, r + 2], ...after] });
  }
  if (g === 1 || g === 2) return tableDSmallGap(g, r, after, p, L);
  // g in {3,4}: rest[0] plays the SAME role as a fresh top-level contact
  // (table A/B/C/D's own precondition entries): recurse through the SAME
  // top-level dispatcher (phase2) on [rest[0], ...after] -- rest is
  // already in preStack form. If the recursive result is a genuine fresh
  // landing (H assigned directly: chunkTerm, cascade, g3term/g4term, g5, a
  // digitBirth2/smallGap1 landing, chunkBig, or a further D:/B: recurse),
  // table D ADOPTS it (top/H/stack as computed) and APPENDS its own [1,5]
  // to whatever W it produced. If the result is a STACK-TRANSFORM
  // continuation (table A/B's g3/g4/g2odd -- still mid-excursion, H just a
  // generic placeholder), table D STAYS (top=4, H=5), takes the
  // sub-result's stack[0] shifted +5 in gap as its OWN new rest[0], and
  // keeps the sub-result's deeper stack untouched. The sub-dispatch's OWN
  // p/L delta is discarded entirely -- table D's single base lap (already
  // applied above) is the only cost paid. Oracle-verified against every
  // real 10M-orbit D:UNIMPLEMENTED instance (rest[0] is always exactly
  // (3,2) there, chaining 1-3 levels deep); c1w-sweep-BD.mjs's isolated
  // single-entry results for OTHER (gap,run) pairs are consistent with
  // this mechanism but not independently re-verified with a sentinel.
  const sub = phase2([[g, r], ...after], p, L);
  if (isContinuation(sub.case)) {
    const [cg, cr] = sub.F.stack[0];
    return mk('D:recurse:' + sub.case, { top: 4, H: 5, p: P, L: L2, stack: [[cg + 5, cr], ...sub.F.stack.slice(1)] });
  }
  return mk('D:recurse:' + sub.case, { top: sub.F.top, H: sub.F.H, W: [...sub.F.W, 1, 5], p: P, L: L2, stack: sub.F.stack });
}

// gap in {1,2}: dense sweep over run=2..9 (c1w-sweep-BD2.mjs). The (4,4)
// contact's own lap depends only on the FOLLOWING entry's gap and run
// parity (never scaled by anything beyond it); ones-count and the shift
// applied to whatever comes after are an exact fit across run=2..9 (and
// gap=2,run=2 -- the would-be (2,2)-chain shape -- already fits this
// same formula uniformly, confirmed against a literal chain of length 1).
function tableDSmallGap(g, r, after, p, L) {
  const even = r % 2 === 0;
  let ones, dp, dL, shift;
  if (g === 1) {
    ones = even ? r / 2 + 1 : (r + 3) / 2;
    dp = even ? -8 : -12; dL = even ? 32 : 48;
    shift = even ? 4 : 5;
  } else {
    ones = Math.floor(r / 2) + 2;
    dp = even ? -16 : -12; dL = even ? 64 : 48;
    shift = even ? 5 : 4;
  }
  const w = [...Array(ones).fill(1), 5];
  const stack = after.length ? [[after[0][0] - shift, after[0][1]], ...after.slice(1)] : [];
  return mk(`D:gap${g}${even ? 'Even' : 'Odd'}`, { top: 2, H: 4, W: w, p: p + dp, L: L + dL, stack });
}

// digitBirth2's evenChain closure for the ONE chain shape every real
// 10M-orbit "gap < 5 after the chain" instance has: chain = [4,6] (trigger
// run 4, one extension to run 6 -- j2 = 0 always in that population).
// Oracle-derived (c1-sweep-db2even-46.mjs), dispatched on beyond = (g,r):
// the entry immediately after the chain, `tail` = whatever is deeper still
// (always passes through untouched, confirmed with a sentinel entry).
//  - g=1: H' promotes to 9 (W' empty); entry becomes [4, r+6].
//  - g=2, r=2 (a free, term-like absorb -- NOT a chain extension since
//    run<4): H'=8, W'=[1,5,9] (the chain's own w9-word plus one more '5'
//    for this absorbed entry), stack consumed to `tail`.
//  - g=2, r odd (even r>=4 would have extended the chain, handled above):
//    H'=5, W'=[9], top'=4; entry becomes [4,r] (run unchanged); `tail`'s
//    first entry (if any) shifts gap -1, mirroring A:g2odd's own shift.
//  - g=3, r=3 or g=4, r=2 (table-A term shapes): consumed to blank, H'=4,
//    W'=[1,5,9], top'=4.
//  - g=3 (r != 3): H'=5, W'=[9], top'=4; entry becomes [3, r+1].
//  - g=4 (r != 2): H'=5, W'=[9], top'=4; entry becomes [3, r+2].
// Returns null for anything outside this closure (caller falls back to the
// -UNVERIFIED tag).
function evenChain46(g, r, tail, p, L, tag) {
  const P = p - 2, L2 = L + 8;
  if (g === 1) return mk(tag, { top: 2, H: 9, W: [], p: P, L: L2, stack: [[4, r + 6], ...tail] });
  if (g === 2 && r === 2) return mk(tag, { top: 2, H: 8, W: [1, 5, 9], p: P, L: L2, stack: tail });
  if (g === 2) return mk(tag, { top: 4, H: 5, W: [9], p: P, L: L2, stack: [[4, r], ...shiftFirst(tail, 1)] });
  if (g === 3 && r === 3) return mk(tag, { top: 4, H: 4, W: [1, 5, 9], p: P, L: L2, stack: tail });
  if (g === 3) return mk(tag, { top: 4, H: 5, W: [9], p: P, L: L2, stack: [[3, r + 1], ...tail] });
  if (g === 4 && r === 2) return mk(tag, { top: 4, H: 4, W: [1, 5, 9], p: P, L: L2, stack: tail });
  if (g === 4) return mk(tag, { top: 4, H: 5, W: [9], p: P, L: L2, stack: [[3, r + 2], ...tail] });
  return null;
}

// Even-run gap-2 entries birth digit 9. H stays 4+4j (j = a leading
// (2,2)-chain within rest, absorbed for free as before) UNLESS what
// follows continues or complicates the birth (oracle-swept exhaustively:
// c1w-sweep-db2nested*.mjs):
//  - tail[j] gap>=5 (the >=6 threshold was actually >=5 all along: gap=5
//    fits the exact same -4 cascade): standard cascade, digit sits in W.
//  - tail[j] gap=2, run even>=4: the birth CONTINUES. Every consecutive
//    such entry (this trigger plus tail[j], tail[j+1], ... while they stay
//    gap=2/even/>=4), deepest first, contributes floor((run-4)/2) ones
//    then a symbol -- '5' at every level except the outermost (the
//    ORIGINAL trigger), which gets '9'. The whole run is consumed
//    together; what follows cascades -4 if gap>=5, else unresolved.
//  - tail[j] gap=1: the digit is CANCELLED (W stays empty) and tail[j]
//    becomes [3, tail[j].run + r] (r = this trigger's own run) -- exact
//    fit for r in {4,8,12}, any tail[j].run; deeper entries pass through
//    unchanged; a DOUBLE lap (not the usual single).
//  - tail[j] gap=2 (odd run), gap=3 (run!=3), or gap=4 (run!=2): the digit
//    is PROMOTED to H' directly (H'=9) -- but ONLY when r===4 and j===0
//    (no leading chain, minimal trigger run). Otherwise (r!=4, or j>0) an
//    extra entry [3, r-2] absorbs the trigger's own excess ones and the
//    promotion does not happen (H stays 4+4j, W=[]); the inner transform
//    keeps its base run adjustment, gap-shifted by 4j when j>0 (single
//    spot check for j>0, the real (2,22)(2,2)(3,2) instance).
//  - tail[j] gap=3,run=3 or gap=4,run=2 (table-A term shapes): the digit
//    stays in W unaffected, H'=4+4j, tail[j] consumes to blank, deeper
//    passes through.
function digitBirth2(r, rest, p, L, k) {
  let j = 0;
  while (j < rest.length && rest[j][0] === 2 && rest[j][1] === 2) j++;
  const after = rest.slice(j + 1);
  const baseH = 4 + 4 * j;
  const tag = k > 0 ? `digitBirth2(k=${k})` : 'digitBirth2';
  const w9 = () => [...Array((r - 4) / 2).fill(1), 9];
  if (j >= rest.length) {
    return mk(tag + ':term', { top: 2, H: baseH, W: w9(), p: p - 2, L: L + 8, stack: [] });
  }
  const [g2, r2] = rest[j];
  if (g2 >= 5) {
    return mk(tag + ':cascade', { top: 2, H: baseH, W: w9(), p: p - 2, L: L + 8, stack: [[g2 - 4, r2], ...after] });
  }
  if (g2 === 2 && r2 % 2 === 0) {
    // A LEADING (2,2)-run before the birth (j>0) does NOT add 4j to H the
    // way the isolated chain does elsewhere -- instead it promotes chain[1]
    // (tail[j] itself) to ALSO use '9' (alongside the true outer). A
    // TRAILING (2,2)-run immediately after the whole even-run chain absorbs
    // for free into H exactly like the ordinary leading-chain scan (oracle:
    // the real (2,22)(2,2)(2,4)(2,2) and (2,4)(2,6)(2,2) instances).
    const chain = [r, r2];
    let idx = j + 1;
    while (idx < rest.length && rest[idx][0] === 2 && rest[idx][1] % 2 === 0 && rest[idx][1] >= 4) {
      chain.push(rest[idx][1]); idx++;
    }
    let j2 = 0;
    while (idx + j2 < rest.length && rest[idx + j2][0] === 2 && rest[idx + j2][1] === 2) j2++;
    const beyond = rest.slice(idx + j2);
    const chainH = 4 + 4 * j2;
    const w = [];
    for (let i = chain.length - 1; i >= 0; i--) {
      for (let n = 0; n < (chain[i] - 4) / 2; n++) w.push(1);
      w.push((i === 0 || (j > 0 && i === 1)) ? 9 : 5);
    }
    if (beyond.length === 0) {
      return mk(tag + ':evenChain:term', { top: 2, H: chainH, W: w, p: p - 2, L: L + 8, stack: [] });
    }
    const [g3, r3] = beyond[0];
    if (g3 >= 5) {
      return mk(tag + ':evenChain:cascade', { top: 2, H: chainH, W: w, p: p - 2, L: L + 8, stack: [[g3 - 4, r3], ...beyond.slice(1)] });
    }
    // gap < 5 after the chain: every real 10M-orbit instance (11x) has
    // chain=[4,6] exactly (one 3-level, chain=[4,6,4], beyond gap=1 only).
    // See evenChain46 for the oracle-derived closure over beyond's category.
    if (chain.length === 2 && chain[0] === 4 && chain[1] === 6) {
      const hit = evenChain46(g3, r3, beyond.slice(1), p, L, tag + ':evenChain:nested');
      if (hit) return hit;
    }
    if (chain.length === 3 && chain[0] === 4 && chain[1] === 6 && chain[2] === 4 && g3 === 1) {
      return mk(tag + ':evenChain:nested3', { top: 4, H: 5, W: [9], p: p - 2, L: L + 8, stack: [[4, r3 + 4], ...beyond.slice(1)] });
    }
    return mk(tag + ':evenChain:nested-UNVERIFIED', { top: 2, H: chainH, W: w, p: p - 2, L: L + 8, stack: beyond });
  }
  if (g2 === 1) {
    return mk(tag + ':nestedGap1', { top: 2, H: baseH, W: [], p: p - 4, L: L + 16, stack: [[3, r2 + r], ...after] });
  }
  if ((g2 === 3 && r2 === 3) || (g2 === 4 && r2 === 2)) {
    return mk(tag + ':nestedTerm', { top: 4, H: baseH, W: w9(), p: p - 2, L: L + 8, stack: after });
  }
  let entry, shiftAfter = 0;
  if (g2 === 2) { entry = [4, r2]; shiftAfter = 1; }
  else if (g2 === 3) { entry = [3, r2 + 1]; }
  else { entry = [3, r2 + 2]; }
  if (r === 4 && j === 0) {
    return mk(tag + ':nestedPromoted', { top: 2, H: 9, W: [], p: p - 2, L: L + 8, stack: [entry, ...shiftFirst(after, shiftAfter)] });
  }
  // r != 4 or j > 0: an extra entry [3, r-2] absorbs the trigger's own
  // excess; the inner transform keeps ITS OWN run adjustment (entry[1]),
  // gap-shifted by 4j when j>0 (verified against every real j>0 instance:
  // (2,22)(2,2)(3,2)/(2,3)/(3,2)(7|3,2) all land here).
  const innerEntry = j > 0 ? [entry[0] + 4 * j, entry[1]] : entry;
  return mk(tag + ':nestedExcess-UNVERIFIED', {
    top: 2, H: 4, W: [], p: p - 4, L: L + 16,
    stack: [[3, r - 2], innerEntry, ...shiftFirst(after, shiftAfter)],
  });
}

// Gap=1 entries mirror gap=2's even/odd split (oracle-swept r=2..7 with a
// gap>=6 sentinel beneath): run=2 is its own terminal (digit 5 born
// directly as H', top'=4, one p-lap, everything deeper untouched -- the
// gap=1 analogue of smallGap3term/smallGap4term). run odd>=3 births digit
// 5 behind floor(r/2) spacer ones, a "triple lap" (p-=6, L+=16... no,
// +24), and shifts the next entry by -4. run even>=4 births the same digit
// word but a "quintuple lap" (p-=10, L+=40) and shifts the next entry by
// -5. k>0 (reached after an outer (2,2) chain), run=2: the r2term case
// generalizes cleanly -- the born digit shifts by +4k (H'=5+4k, matching
// the smallGap3term/g4term/A:g5 "4k+8"-family pattern one rung down),
// single lap, deeper stack untouched (confirmed against the real
// ev717 instance AND every real orbit hop that recurses through it via
// tableCGeneric at scale, e.g. ev2039246). run!=2 with k>0 is unverified.
function smallGap1(r, rest, p, L, k) {
  if (k > 0 && r === 2) {
    return mk(`smallGap1:r2term(k=${k})`, { top: 4, H: 5 + 4 * k, p: p - 2, L: L + 8, stack: rest });
  }
  if (k > 0) {
    return mk(`smallGap1(k=${k})-UNVERIFIED`, {
      top: 2, H: 4, p: p - 4, L: L + 16, stack: [[3 + 4 * k, 6], ...rest],
    });
  }
  if (r === 2) {
    return mk('smallGap1:r2term', { top: 4, H: 5, p: p - 2, L: L + 8, stack: rest });
  }
  const w = [...Array(Math.floor(r / 2)).fill(1), 5];
  const odd = r % 2 === 1;
  const shift = odd ? 4 : 5;
  const lapP = odd ? p - 6 : p - 10;
  const lapL = odd ? L + 24 : L + 40;
  if (rest.length === 0) {
    return mk(`smallGap1:${odd ? 'odd' : 'even'}Term`, { top: 2, H: 4, W: w, p: lapP, L: lapL, stack: [] });
  }
  const [g2, r2] = rest[0];
  return mk(`smallGap1:${odd ? 'odd' : 'even'}`, { top: 2, H: 4, W: w, p: lapP, L: lapL, stack: [[g2 - shift, r2], ...rest.slice(1)] });
}

// F.p === 0: the 8/1095 epoch-phase boundary states (grammar census). The
// single-step MACHINERY is proven in Coq (mstep_absorb_nil, mstep_skim,
// mstep_absorb_rs0, the unwind -- coq/ParityHops.v); this is the F-level
// successor law, reverse-engineered by oracle replay of synthetic p0
// states (c1w-sweep-epoch*.mjs) and cross-checked against the 7 real p0
// instances in the 10M orbit. p' is always F.L/2 plus a small,
// rule-dependent offset; L' is always a small constant (also
// rule-dependent) -- never the usual lap arithmetic.
// Covers 6 of the 7 real instances. The 7th (ev1959320: a 5-entry stack
// whose first three entries collapse through a digit-9 birth before a
// plain cascade) is NOT resolved -- see the report's "epoch: what's left"
// section and epoch:p0-deepChain-UNIMPLEMENTED.
function epoch(F) {
  const { H, top, L, stack } = F;
  const half = L / 2;
  if (stack.length === 0) {
    if (H === 4) return mk('epoch:p0-blank', { top: 2, H: 4, p: half, L: 16, stack: [] });
    if (H === 5) return mk('epoch:p0-blankH5', { top: 2, H: 8, p: half, L: 8, stack: [] });
    return mk('epoch:p0-blankBig', { top: 2, H: 4, p: half, L: 8, stack: [[H - 7, top]] });
  }
  const [g, r] = stack[0];
  const rest = stack.slice(1);
  if (g >= 6) {
    if (H === 5) return mk('epoch:p0-bigH5', { top: 2, H: 4, W: [5], p: half, L: 8, stack: [[g - 4, r], ...rest] });
    return mk('epoch:p0-big', { top: 2, H: 4, p: half, L: 16, stack: [[g - 5, r], ...rest] });
  }
  if (g === 2 && r === 2 && H === 4) {
    return mk('epoch:p0-chain', { top: 2, H: 4, p: half, L: 24, stack: rest });
  }
  if (g === 2 && r === 2 && H === 5) {
    return mk('epoch:p0-chainH5-UNVERIFIED', { top: 2, H: 12, p: half, L: 8, stack: rest });
  }
  if (g === 2 && r % 2 === 1) {
    return mk('epoch:p0-g2odd', { top: 2, H: 4, p: half + 2, L: 20, stack: shiftFirst(rest, 4) });
  }
  if ((g === 3 && r !== 3) || (g === 4 && r !== 2)) {
    if (H === 5) {
      return mk('epoch:p0-continuation', { top: 2, H: 4, p: half - 2, L: 16, stack: [[2, r + 1], ...rest] });
    }
    // H === 4: the H=5 formula above does NOT generalize -- it silently
    // drops the rest of the stack, which is fine when H=5 (oracle-confirmed
    // deeper is always inert there) but wrong when H=4 (deeper entries get
    // absorbed). Deep chain: consecutive (gap=2, EVEN run) entries right
    // after stack[0] each absorb like a table-D base lap (p -= 8, L += 32)
    // and contribute floor(run/2)+1 ones to W; the chain ends at the first
    // entry with gap >= 6 (its own gap shifts -5, run unchanged). r odd
    // seeds the word with floor((r-3)/2) ones before the chain's own.
    // Oracle-verified for 1-3 absorbed entries (c1-sweep-epoch3/4.mjs),
    // matching the one real 10M-orbit instance (ev1959320) exactly; r even,
    // g===4, or a chain that never reaches a gap>=6 entry are NOT covered.
    if (H === 4 && g === 3 && r % 2 === 1) {
      let i = 0, ones = Math.floor((r - 3) / 2), chainCount = 0;
      while (i < rest.length && rest[i][0] === 2 && rest[i][1] % 2 === 0) {
        ones += Math.floor(rest[i][1] / 2) + 1;
        chainCount++; i++;
      }
      if (i < rest.length && rest[i][0] >= 6) {
        const [lg, lr] = rest[i];
        return mk('epoch:p0-deepChain', {
          top: 2, H: 4, W: [...Array(ones).fill(1), 5],
          p: half - 4 - 8 * chainCount, L: 32 * (1 + chainCount),
          stack: [[lg - 5, lr], ...rest.slice(i + 1)],
        });
      }
    }
  }
  return { case: 'epoch:p0-deepChain-UNIMPLEMENTED', F: null };
}

function fEqual(a, b) {
  if (!a || !b) return a === b;
  return a.top === b.top && a.H === b.H && a.p === b.p && a.L === b.L
    && a.W.length === b.W.length && a.W.every((v, i) => v === b.W[i])
    && a.stack.length === b.stack.length
    && a.stack.every(([g, r], i) => b.stack[i][0] === g && b.stack[i][1] === r);
}

// Human-readable rule text per case key, for chunkstep-cases.json. Matched
// by prefix since digitBirth2/smallGap1 tag k and phase1 tags the close
// count into the key itself.
const CASE_RULES = [
  [/^phase1:closed=/, "Phase 1 lands the next boundary mid-prefix: H then some of W get 'closed' " +
    "(top' = 2 or 4) and the very next un-consumed symbol is itself >= 4, so it becomes H' directly. " +
    "p, L untouched; stack gains one new (gap,run) entry per closed symbol (gap = symbol-1, run = the " +
    "fresh run at the moment it closed), shallowest entry last-closed."],
  [/^chunkBig$/, "H in {9} u {4c+8: c>=0}, any top, p>=2: chunkBig (coq/Parity.v), generalized from H=4c+8 " +
    "to H=9. H'=4, p'=p-2, L'=L+8, push [H-6, top] onto stack (deeper stack untouched)."],
  [/^A:cleanK0$/, "H=4, top=2, F.stack=[] or F.stack[0].gap>=6, reached with zero (2,2) entries absorbed: " +
    "H'=4, p'=p-2, L'=L+8, push [F.stack[0].gap-4, F.stack[0].run] (deeper untouched)."],
  [/^A:chunkCascade$/, "H=4, top=2: F.stack starts with k>=1 entries of (gap=2,run=2) then an entry with " +
    "gap>=6 (generalizes chunkCascade's 4c+6). H'=4k+8, p'=p-2, L'=L+8, the k (2,2)'s pop, the terminating " +
    "entry's gap -= 4 (run unchanged), deeper untouched."],
  [/^A:chunkTerm$/, "H=4, top=2: F.stack is exactly k>=0 entries of (2,2) then blank (chunkTerm). " +
    "H'=4k+8, top'=2, stack'=[], p'=p-2, L'=L+8."],
  [/^A:g3term$/, "H=4, top=2, after k (2,2)'s the next entry is (gap=3,run=3): consumed entirely " +
    "(no replacement). H'=4k+8, top'=4, p'=p-2, L'=L+8, rest of stack passes through unchanged one level shallower."],
  [/^A:g4term$/, "H=4, top=2, after k (2,2)'s the next entry is (gap=4,run=2): consumed entirely, " +
    "same law as A:g3term. H'=4k+8, top'=4, p'=p-2, L'=L+8."],
  [/^A:g3$/, "H=4, top=2, after k (2,2)'s the next entry is (gap=3, run != 3): H'=4 (k has no effect on H " +
    "here), p'=p-4, L'=L+16 (a double lap), entry becomes [2+4k, run+1], rest of stack unchanged."],
  [/^A:g4$/, "H=4, top=2, after k (2,2)'s the next entry is (gap=4, run != 2): same law as A:g3, " +
    "entry becomes [2+4k, run+1]."],
  [/^A:g5$/, "H=4, top=2, after k (2,2)'s the next entry has gap=5 (any run): H'=4k+8, p'=p-2, L'=L+8, " +
    "entry becomes [1, run] (deeper untouched)."],
  [/^A:g2odd$/, "H=4, top=2, after k (2,2)'s the next entry is (gap=2, run odd>=3): H'=4, p'=p-4, L'=L+16, " +
    "entry becomes [3+4k, run] (run unchanged); the entry AFTER that (if any) has its gap shifted by -1 " +
    "(run unchanged), everything deeper than THAT passes through."],
  [/^(A:g3|A:g4|A:g2odd)-p2underflow$/, "the g3/g4/g2odd double lap (p -= 4) with F.p EXACTLY 2 going in: " +
    "the second half of the lap runs out of p mid-excursion and falls through to an epoch-like landing. " +
    "H'=4, W'=[], top'=2, p'=L/2+4, L'=8 (a fixed constant, NOT the usual lap arithmetic) REGARDLESS of " +
    "the entry or k. The entry itself: A:g3/A:g4 collapse gap to 1 with run shifted +1/+2 (same shift as " +
    "their own non-underflow rule); A:g2odd leaves the entry fully untouched (gap=2, run unchanged) but " +
    "still shifts the NEXT entry's gap -1, mirroring its own non-underflow rule. Oracle-verified " +
    "(c1-sweep-p2.mjs) at k=0 against both real 10M-orbit instances (ev7212 A:g3, ev471436 A:g2odd, the " +
    "only two double-lap underflows in 10M events); k>0 is untested (k does not affect the non-underflow " +
    "p/L either, so assumed immaterial here, but not oracle-checked)."],
  [/^digitBirth2:term/, "gap=2, run even>=4 (digit-9 birth), nothing beyond but j trailing (2,2)'s: " +
    "H'=4+4j, W'=[1 x (run-4)/2, 9], p'=p-2, L'=L+8, stack'=[]."],
  [/^digitBirth2:cascade/, "gap=2, run even>=4 (digit-9 birth), j trailing (2,2)'s then a gap>=6 entry: " +
    "H'=4+4j, W'=[1 x (run-4)/2, 9], p'=p-2, L'=L+8, that entry's gap -= 4 (run unchanged), deeper untouched."],
  [/^digitBirth2\S*:evenChain:(term|cascade)/, "gap=2, run even>=4, tail[j] is ALSO gap=2/even/>=4: the " +
    "birth continues -- every consecutive such entry (deepest first) contributes floor((run-4)/2) ones " +
    "then a symbol ('5' at every level except the outermost/original trigger, which gets '9'); consumed " +
    "together, H'=4+4j, what follows the whole run cascades -4 if gap>=5 (:cascade) or stack'=[] (:term)."],
  [/^digitBirth2\S*:evenChain:nested$/, "as evenChain above, but what follows the whole even-run chain " +
    "(the FIRST entry past it, 'beyond') has gap<5. Resolved for the ONE chain shape every real 10M-orbit " +
    "instance has: chain=[4,6] (trigger run 4, one extension to run 6). Dispatched on beyond=(g,r): g=1 " +
    "promotes H' to 9 (W' empty), entry becomes [4,r+6]; g=2,r=2 is a free absorb (H'=8, W'=[1,5,9], " +
    "stack consumed to whatever is deeper); g=2 odd r lands H'=5,W'=[9],top'=4, entry becomes [4,r] (run " +
    "unchanged), and the NEXT entry (if any) shifts gap -1; g=3,r=3 or g=4,r=2 (table-A term shapes) " +
    "consume to blank (H'=4,W'=[1,5,9],top'=4); g=3 otherwise lands H'=5,W'=[9],top'=4, entry becomes " +
    "[3,r+1]; g=4 otherwise the same with entry [3,r+2]. Deeper-than-beyond entries always pass through " +
    "untouched (confirmed with a sentinel). Oracle-derived (c1-sweep-db2even-46.mjs), matches all 10 " +
    "real 2-level 10M-orbit instances exactly; chain shapes other than [4,6] fall through to " +
    "':evenChain:nested-UNVERIFIED' (never hit in 10M events)."],
  [/^digitBirth2\S*:evenChain:nested3$/, "a THIRD chain level (chain=[4,6,4]) with beyond gap=1: the one " +
    "real 3-level 10M-orbit instance (ev268327). H'=5, W'=[9], top'=4, entry becomes [4,r+4] (r = beyond's " +
    "run); deeper passes through untouched (sentinel-checked). Oracle-derived, verified for beyond gap=1 " +
    "only -- other beyond shapes at chain-length 3 were spot-checked during derivation but are NOT wired " +
    "in (not needed, never hit in 10M events)."],
  [/^digitBirth2\S*:evenChain:nested-UNVERIFIED/, "as evenChain above, but what follows the whole even-run " +
    "chain has gap<5 AND the chain isn't [4,6] (2-level) or [4,6,4]-with-beyond-gap-1 (3-level): " +
    "UNRESOLVED (not hit in the 10M orbit -- every real instance matches one of the two resolved shapes " +
    "above)."],
  [/^digitBirth2\S*:nestedGap1/, "gap=2, run even>=4, tail[j] has gap=1: the digit-9 is CANCELLED (W " +
    "stays empty) and tail[j] becomes [3, tail[j].run + r] (r = the trigger's own run); deeper entries " +
    "pass through unchanged; a DOUBLE lap (p-=4, L+=16), not the usual single."],
  [/^digitBirth2\S*:nestedTerm/, "gap=2, run even>=4, tail[j] is a table-A term shape (gap=3,run=3 or " +
    "gap=4,run=2): the digit-9 sits in W unaffected, H'=4+4j, tail[j] consumes to blank, deeper passes through."],
  [/^digitBirth2\S*:nestedPromoted/, "gap=2, run EXACTLY 4, no leading (2,2)-chain (j=0), tail[j] is gap=2 " +
    "(odd run) / gap=3 (run!=3) / gap=4 (run!=2): the digit-9 is PROMOTED to H' directly (H'=9, top'=2, " +
    "W'=[]); tail[j] becomes [4,run] (gap2-odd, next entry gap-=1) / [3,run+1] (gap3) / [3,run+2] (gap4)."],
  [/^digitBirth2\S*:nestedExcess-UNVERIFIED/, "as nestedPromoted's trigger shapes, but run != 4 or j>0 " +
    "(the trigger has 'excess' beyond the minimal case): the promotion does NOT happen -- an extra entry " +
    "[3, run-2] absorbs the excess, H stays 4+4j, W=[]; a DOUBLE lap. Oracle-verified for run!=4,j=0 " +
    "(c1w-sweep-db2nested3.mjs); the j>0 gap-shift (+4j, dropping the run adjustment) is a single spot " +
    "check against one real instance (ev1959320's (2,22)(2,2)(3,2))."],
  [/^smallGap1:r2term/, "gap=1, run=2 (the gap=1 analogue of A:g3term/A:g4term): digit 5 born directly as " +
    "H' (not via W), top'=4, p'=p-2, L'=L+8, deeper stack untouched."],
  [/^smallGap1:odd(?!.*Term)/, "gap=1, run odd>=3, something deeper: W'=[1 x floor(run/2), 5], p'=p-6, " +
    "L'=L+24 (triple lap), next entry's gap -= 4 (run unchanged)."],
  [/^smallGap1:oddTerm/, "gap=1, run odd>=3, nothing deeper: W'=[1 x floor(run/2), 5], p'=p-6, L'=L+24, stack'=[]."],
  [/^smallGap1:even(?!.*Term)/, "gap=1, run even>=4, something deeper: W'=[1 x floor(run/2), 5], p'=p-10, " +
    "L'=L+40 (quintuple lap), next entry's gap -= 5 (run unchanged)."],
  [/^smallGap1:evenTerm/, "gap=1, run even>=4, nothing deeper: W'=[1 x floor(run/2), 5], p'=p-10, L'=L+40, stack'=[]."],
  [/^smallGap1\(k=/, "gap=1 reached after an outer (2,2) chain (k>0): UNVERIFIED, single spot check only (k=1)."],
  [/^gap1-offgrammar/, "gap=1 with run outside the grammar's observed set: not implemented (never seen in 2M+ events)."],
  [/^C:shift1$/, "H=5, top=2 (preStack[0]=(4,2)): uniform regardless of what follows (blank or ANY gap, " +
    "oracle-checked at gap in {3,5,7}): top'=4, H'=4, p'=p-6, L'=L+24 (triple lap), next entry's gap -= 1 " +
    "(run unchanged) if it exists."],
  [/^C:blank$/, "H=5, top=2, F.stack=[]: top'=4, H'=4, p'=p-6, L'=L+24, stack'=[]."],
  [/^C:shift1-EXTRAPOLATED$/, "gap=4 reached via a digit-5 Phase-1 closure with an ACCUMULATED run (not " +
    "F.top in {2,4}): the entry is a free absorb (its exact run value never resurfaces -- oracle-swept at " +
    "r0 in {6,8,...,30}), and the excursion re-enters exactly the top-level dispatch (phase2) on rest[0]; " +
    "whatever lap that sub-dispatch computes gets scaled by exactly 4x, shape (top,H,W,stack) passes " +
    "through unchanged. c1w-sweep-shift1x.mjs. Only correct when the sub-dispatch is a FRESH landing " +
    "(isContinuation(sub.case) false) or is a continuation shape NOT covered by the two special cases " +
    "below; both real 10M-orbit continuation instances need one of those instead."],
  [/^C:shift1-EXTRAPOLATED:continuation-Ag3-p8$/, "as C:shift1-EXTRAPOLATED, but the sub-dispatch is " +
    "'A:g3' (a continuation, not a fresh landing) and F.p is EXACTLY 8: the naive 4x scaling above would " +
    "need p>=16 (dp=4, scaled 4x) and underflows. H'=4, top'=2, W'=[1 x (k-1), 5] (k=(r0-2)/2), " +
    "p'=L/2+16, L'=8 (fixed, epoch-like -- not the usual lap arithmetic); the stack is rest[1] " +
    "(the RAW entry the sub-dispatch would have shifted, gap UNCHANGED, run+1) followed by rest.slice(2) " +
    "untouched. Oracle-derived (c1-sweep-cgeneric.mjs) at exactly p=8; matches the one real 10M-orbit " +
    "instance (ev7551768). Other p in the underflow range (p<16) were swept and show multiple further " +
    "regimes (not a single clean formula) -- NOT implemented, since p=8 is the only value hit in 10M " +
    "events."],
  [/^C:shift1-EXTRAPOLATED:continuation-nestedGap1$/, "as C:shift1-EXTRAPOLATED, but the sub-dispatch is " +
    "'digitBirth2:nestedGap1' (a continuation) with the gap1-partner's run EXACTLY 2 and a leading (2,2) " +
    "before it (j>=1, i.e. rest[2..] starts with at least one explicit (2,2) before the gap=1 entry): the " +
    "naive 4x scaling produces the wrong shape (it does not underflow, but wrongly treats the mid-" +
    "excursion continuation as fresh). Resolves to EXACTLY table D's own base lap regardless of r0: " +
    "top'=4, H'=5, p'=p-8, L'=L+32; W'=[1 x (trigR-4)/2, 9, 1 x (r0-2)/2, 5] (trigR = the digitBirth2 " +
    "trigger's own run, rest[1].run); stack'= whatever is deeper than the gap1 entry, untouched. j===0 " +
    "(no leading (2,2)) is a DIFFERENT shape where the naive formula above is actually already correct " +
    "(oracle-confirmed against a second real 10M instance, ev2275572) -- do not extend this branch to " +
    "j=0. Oracle-derived (c1-sweep-cgeneric2/3.mjs); matches the one real j>=1 10M-orbit instance " +
    "(ev8351703) exactly."],
  [/^B:blank$|^B:big$|^B:g[34]term$/, "H=4, top=4 (preStack[0]=(3,4)): a leading (2,2)-chain (j entries) " +
    "is absorbed into H (H'=4+4j) exactly like table A's; the contact's own cost is ALWAYS a single base " +
    "lap (p-=2, L+=8), never scaled. blank/gap>=5/term-shapes land digit 5 in W (or leave it there " +
    "unaffected for gap>=5, shifted -4), H'=4+4j, top'=2."],
  [/^B:g[234]/, "H=4, top=4, tail[j] has gap in {2 (odd), 3 (run!=3), 4 (run!=2)}: the digit 5 is promoted " +
    "to H' directly (H'=5, top'=2); tail[j] becomes [4,run] (gap2, next entry gap-=1) / [3+4j,run+1] " +
    "(gap3) / [3+4j,run+2] (gap4)."],
  [/^B:evenChain:(term|cascade)/, "H=4, top=4, tail[j] is gap=2/even/>=4: the birth continues (same " +
    "deepest-first construction as digitBirth2's own even-chain), but EVERY level uses '5' -- table B's " +
    "base birth is a separate extra '5' appended last; H'=4+4j, what follows cascades -4 if gap>=5."],
  [/^B:evenChain:nested$/, "as B's evenChain above, but what follows the chain (a SINGLE-level chain, " +
    "run r >= 8, no extension) has gap<5, with exactly one leading AND one trailing (2,2) (j = j2 = 1) -- " +
    "the ONE shape every real 10M-orbit instance (3x) has. The chain's own outer entry becomes " +
    "[4+4j, r-2] (mirrors digitBirth2's r2>=8 'extra entry' regime one level up, but table B's promoted " +
    "digit is always '5', never '9') and sits ahead of beyond's own transform: g=1 -> [4,run+2]; g=2 odd " +
    "run -> [8,run] (run unchanged), and the entry after beyond (if any) shifts gap -1; g=3 -> " +
    "[7,run+1]; g=4 -> [7,run+2]. g=3,run=3 or g=4,run=2 (term shapes) instead fold BOTH the chain's " +
    "outer entry and beyond into W (H'=4+4j, W'=[1 x (r-4)/2, 9, 5], stack consumed to whatever is " +
    "deeper). Oracle-derived (c1-sweep-tableB-even.mjs); a chain run < 8, an extended (multi-level) " +
    "chain, or j/j2 != 1 falls through to ':evenChain:nested-UNVERIFIED' (never hit in 10M events)."],
  [/^B:evenChain:nested-UNVERIFIED/, "as B's evenChain above, but what follows has gap<5 AND the chain " +
    "isn't the single shape resolved above (run>=8, j=j2=1): UNRESOLVED (not hit in the 10M orbit)."],
  [/^D:blank$|^D:big$|^D:g5/, "H=5, top=4 (preStack[0]=(4,4)): the contact ALWAYS costs exactly one base " +
    "lap (p-=8, L+=32), never scaled by anything past it. blank/gap>=6 births [1,5] in W (gap>=6 shifts " +
    "-5); gap=5,run=2 consumes to blank; gap=5,run>=3 lands the digit as H'=5 directly, entry [3,run+2]."],
  [/^D:gap[12]/, "H=5, top=4, tail[0] has gap in {1,2}: dense sweep over run=2..9 -- ones-count and the " +
    "lap (which depends on run's parity, not magnitude) are an exact fit; the entry beyond shifts by 4 or " +
    "5 depending on gap/parity (c1w-sweep-BD2.mjs)."],
  [/^D:recurse:/, "H=5, top=4, rest[0] has gap in {3,4}: rest[0] plays the SAME role as a fresh top-level " +
    "contact -- recurse through phase2 on [rest[0],...after]. A genuine fresh landing (H assigned " +
    "directly) is ADOPTED (top/H/stack as computed) with table D's own [1,5] appended to W; a " +
    "stack-transform continuation (g3/g4/g2odd) leaves table D staying (top=4,H=5), taking the " +
    "sub-result's stack[0] shifted +5 in gap. Sub-dispatch's own p/L delta is discarded -- only table D's " +
    "single base lap is paid. Verified against every real 10M D:UNIMPLEMENTED instance (rest[0] always " +
    "(3,2) there, chaining 1-3 levels); other (gap,run) pairs match the isolated single-entry oracle " +
    "sweep but aren't independently re-verified with a sentinel."],
  [/^epoch:p0-blank$|^epoch:p0-blankH5$|^epoch:p0-blankBig$|^epoch:p0-big$|^epoch:p0-bigH5$|^epoch:p0-chain$|^epoch:p0-g2odd$|^epoch:p0-continuation$/,
    "F.p = 0 (the 8/1095 epoch-phase boundary states): p'=F.L/2 plus a small rule-dependent offset " +
    "(0 for blank/big/chain, +2 for a consumed gap=2-odd entry, -2 for a gap-3/4 'continuation' transform " +
    "in place); L' is a small rule-dependent constant (16 base for H=4, 8 for H=5-triggered births, +8 " +
    "for a consumed (2,2), +4 for a consumed gap=2-odd). Reverse-engineered by oracle replay of synthetic " +
    "p0 states (c1w-sweep-epoch*.mjs); covers 6 of the 7 real 10M-orbit instances exactly. NOTE: " +
    "'epoch:p0-continuation' (the gap-3/4 transform) is proven ONLY for H=5 here -- oracle-confirmed that " +
    "deeper stack entries are always inert for H=5 regardless of shape. H=4 does NOT reduce to this " +
    "formula; see epoch:p0-deepChain."],
  [/^epoch:p0-chainH5-UNVERIFIED/, "F.p=0, F.stack[0]=(2,2), H=5: single oracle spot check only (no real " +
    "orbit instance)."],
  [/^epoch:p0-deepChain$/, "F.p=0, H=4, F.stack[0]=(gap=3, ODD run != 3) -- the H=4 counterpart of " +
    "epoch:p0-continuation, where (unlike H=5) deeper entries are NOT inert. Consecutive (gap=2, EVEN " +
    "run) entries right after stack[0] each absorb like a table-D base lap (p -= 8, L += 32) and " +
    "contribute floor(run/2)+1 ones to W; the chain ends at the first entry with gap>=6 (its own gap " +
    "shifts -5, run unchanged); stack[0]'s own odd run seeds the word with floor((r-3)/2) ones before the " +
    "chain's own. H'=4, top'=2, p'=F.L/2-4-8*(chain length), L'=32*(1+chain length). Oracle-verified for " +
    "1-3 absorbed entries (c1-sweep-epoch3/4.mjs); matches the one real 10M-orbit instance (ev1959320, a " +
    "2-entry chain) exactly. r even, g=4, H not in {4,5}, or a chain that never reaches a gap>=6 entry " +
    "fall through to epoch:p0-deepChain-UNIMPLEMENTED (none hit in 10M events)."],
  [/^epoch:p0-deepChain-UNIMPLEMENTED/, "F.p=0, F.stack[0] doesn't match any of the characterized shapes " +
    "(blank / gap>=6 / (2,2) / gap=2-odd / H=5 gap-3-or-4-continuation / H=4 odd-gap3-deepChain): NOT " +
    "IMPLEMENTED. No real 10M-orbit instance hits this branch (all 7 real p0 boundaries are covered by " +
    "the resolved cases above)."],
];
function describeCase(key) {
  for (const [re, text] of CASE_RULES) if (re.test(key)) return text;
  return '(no description written for this case key)';
}
function caseSideConditions(key) {
  const cond = [];
  if (/UNVERIFIED|UNIMPLEMENTED/.test(key)) {
    cond.push('NOT fully oracle-verified -- see rule text and any MISMATCH log lines for this key.');
  }
  if (/^A:g3$|^A:g4$|^A:g2odd$/.test(key)) {
    cond.push('requires F.p >= 4 going in (double lap); F.p === 2 here underflows into the -p2underflow case key instead (resolved, see that key).');
  }
  if (/-p2underflow$/.test(key)) {
    cond.push('k > 0 (a leading (2,2)-chain before the double-lap entry) is untested; verified only at k = 0, matching both real 10M-orbit instances.');
  }
  if (/^digitBirth2\S*:evenChain:nested$|^digitBirth2\S*:evenChain:nested3$|^B:evenChain:nested$/.test(key)) {
    cond.push('verified only for the exact chain shape named in the rule text (the one every real 10M-orbit instance has); other chain shapes fall through to the -UNVERIFIED key.');
  }
  if (/^epoch:p0-deepChain$/.test(key)) {
    cond.push('verified only for H=4, stack[0] gap=3 odd run, a chain of 1-3 EVEN-run absorbed entries ending on a gap>=6 landing; other H=4 continuation shapes fall through to -UNIMPLEMENTED.');
  }
  if (/^C:shift1-EXTRAPOLATED:continuation-/.test(key)) {
    cond.push('re-derives its inputs directly from `rest`, not from the sub-dispatch result -- see the rule text for the exact structural gate (both are narrow, single-instance-verified fixes).');
  }
  if (/^D:recurse:/.test(key)) {
    cond.push("inherits whatever side conditions the recursed-into case (the suffix after 'D:recurse:') carries.");
  }
  if (/^(chunkBig|A:|C:shift1|C:blank|digitBirth2|smallGap1)/.test(key) && !/UNVERIFIED|EXTRAPOLATED|underflow/.test(key)) {
    cond.push('requires F.p >= 2 going in (chunkBig/Parity.v precondition); F.p === 0 is the separate epoch case.');
  }
  return cond;
}

// Exported for throwaway oracle/analysis drivers (outside this repo) that
// need to replay chunkstep/mstepR on synthetic F-states; no effect on the
// CLI modes below.
export {
  mstepR, parseF, chunkstep, phase2, tableA, tableB, tableC, tableD,
  tableCGeneric, tableBEvenBirth, tableBEvenNested, tableDSmallGap,
  digitBirth2, evenChain46, smallGap1, epoch, isContinuation, p2Underflow,
  shiftFirst, fEqual, wallStr, rsStr,
};

if (MODE === '--chunkstep') {
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  let prev = null, boundaries = 0, mismatches = 0;
  let firstBoundary = null;
  const cases = new Map();
  const mismatchEx = [];
  for (let ev = 0; ev < N; ev++) {
    const F = parseF(s);
    if (F) {
      boundaries++;
      if (!firstBoundary) firstBoundary = { ev, F };
      if (prev) {
        const { F: predicted, case: key } = chunkstep(prev);
        if (!cases.has(key)) cases.set(key, { n: 0, examples: [] });
        const c = cases.get(key);
        c.n++;
        if (c.examples.length < 3) c.examples.push({ before: prev, after: F });
        if (!fEqual(predicted, F)) {
          mismatches++;
          c.bad = (c.bad ?? 0) + 1;
          if (mismatchEx.length < 30) {
            mismatchEx.push({ ev, key, before: prev, predicted, actual: F });
          }
        }
      }
      prev = F;
    }
    const nxt = mstepR(s);
    if (!nxt) { console.log(`STUCK at ${ev}`); break; }
    s = nxt;
  }
  console.log(`${N} events, ${boundaries} boundaries, ${boundaries - 1} hops checked, ${mismatches} mismatches`);
  console.log(`first boundary: ev${firstBoundary.ev} ${JSON.stringify(firstBoundary.F)}`);
  const sorted = [...cases].sort((a, b) => b[1].n - a[1].n);
  for (const [key, c] of sorted) console.log(`  ${String(c.n).padStart(7)}x ${key}${c.bad ? `  (${c.bad} MISMATCH)` : ''}`);
  for (const m of mismatchEx) {
    console.log(`MISMATCH ev${m.ev} case=${m.key}`);
    console.log(`  before:    ${JSON.stringify(m.before)}`);
    console.log(`  predicted: ${JSON.stringify(m.predicted)}`);
    console.log(`  actual:    ${JSON.stringify(m.actual)}`);
  }
  const outPath = new URL('./chunkstep-cases.json', import.meta.url);
  const outCases = sorted.map(([key, c]) => ({
    key,
    count: c.n,
    mismatches: c.bad ?? 0,
    rule: describeCase(key),
    sideConditions: caseSideConditions(key),
    examples: c.examples.map(({ before, after }) => ({ before, after })),
  }));
  writeFileSync(outPath, JSON.stringify(outCases, null, 2));
  console.log(`wrote ${outPath.pathname}`);
} else if (MODE === '--roundtrace') {
  // print every mst state from one canonical base to the next, RLE-compact
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  const isBase = st => st.m === 'C' && st.wall.length === 1 && st.wall[0][1] === 2
    && st.rs.length > 1 && st.rs[0] % 4 === 0 && st.rs[0] > 0;
  const rsRle = rs => {
    const out = [];
    for (const v of rs) {
      if (out.length && out[out.length - 1][0] === v) out[out.length - 1][1]++;
      else out.push([v, 1]);
    }
    return out.map(([v, n]) => (n === 1 ? `${v}` : `${v}x${n}`)).join(' ');
  };
  let ev = 0, seen = 0, tracing = false;
  const target = Number(args[2] ?? 3);   // trace the target-th base-to-base round
  for (; ev < N; ev++) {
    if (isBase(s)) {
      seen++;
      if (seen === target) tracing = true;
      else if (tracing) { console.log(`ev ${ev} BASE  C [${wallStr(s.wall)}] ${rsRle(s.rs)}`); break; }
    }
    if (tracing) console.log(`ev ${ev} ${s.m} [${wallStr(s.wall, 20)}] ${rsRle(s.rs).slice(0, 110)}`);
    s = mstepR(s);
    if (!s) break;
  }
} else if (MODE === '--recur') {
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  let prev = null;
  for (let ev = 0; ev < N; ev++) {
    if (s.m === 'C' && s.wall.length === 1 && s.wall[0][1] === 2 && s.rs.length > 1 && s.rs[0] % 4 === 0) {
      // canonical base: C [1^2] [H, ...mid..., 1^K, L]
      const rs = s.rs;
      const H = rs[0];
      const L = rs[rs.length - 1];
      let K = 0, i = rs.length - 2;
      while (i >= 0 && rs[i] === 1) { K++; i--; }
      const W = rs.slice(1, i + 1).join('.');
      const cur = { ev, H, K, L, W };
      let d = '';
      if (prev) d = `  dH=${H - prev.H} dK=${K - prev.K} dL=${L - prev.L}`;
      console.log(`ev ${ev}: H=${H} W=[${W}] K=${K} L=${L}${d}`);
      prev = cur;
    }
    s = mstepR(s);
    if (!s) break;
  }
} else if (MODE === '--grammar') {
  // Parse every boundary state into F-params; census conditions.
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  const bad = [];
  const cen = new Map();
  const note = k => cen.set(k, (cen.get(k) ?? 0) + 1);
  let boundaries = 0;
  for (let ev = 0; ev < N; ev++) {
    if (s.m === 'C' && s.wall[0][0] === 1 && (s.wall[0][1] === 2 || s.wall[0][1] === 4)
        && s.rs.length >= 2 && s.rs[0] >= 4) {
      boundaries++;
      const top = s.wall[0][1];
      // wall: alternating (0^g, 1^r) pairs after the top
      const gs = [];
      let ok = true;
      for (let i = 1; i < s.wall.length; i += 2) {
        if (s.wall[i][0] !== 0 || !s.wall[i + 1] || s.wall[i + 1][0] !== 1) { ok = false; break; }
        gs.push([s.wall[i][1], s.wall[i + 1][1]]);
      }
      if (s.wall.length % 2 === 0) ok = false;   // must end with a 1-run
      // rs: H, W in {1,5,9}*, 1^p, L
      const rs = s.rs;
      const H = rs[0], L = rs[rs.length - 1];
      let p = 0, i = rs.length - 2;
      while (i >= 1 && rs[i] === 1) { p++; i--; }
      const W = rs.slice(1, i + 1);
      if (!W.every(v => v === 1 || v === 5 || v === 9)) ok = false;
      if (L % 4 !== 0 || L < 4) ok = false;
      if (!(H === 4 || H === 5 || H === 9 || (H % 4 === 0 && H >= 8))) ok = false;
      if (!ok) { if (bad.length < 8) bad.push(`ev${ev} ${s.m} [${wallStr(s.wall)}] rs=[${rsStr(s.rs)}]`); }
      else {
        if (p % 2 === 1 && bad.length < 8) bad.push(`ODDP ev${ev} top=${top} H=${H} W=[${W}] p=${p} L=${L} gs=[${gs.map(x=>x.join(':')).join(' ')}]`);
        note(`top=${top}`);
        note(`H=${H <= 9 ? H : 'Q'}`);
        note(`p%2=${p % 2}${p === 0 ? ' p0' : ''}`);
        for (const [g, r] of gs) note(`entry g${g <= 3 ? g : g % 4 === 0 ? 'Q' : g % 4 === 3 ? 'B' : 'g' + (g % 4)} r${r <= 4 ? r : 'X'}${r > 2 ? ' rBIG' : ''}`);
        if (W.length) {
          const wsig = W.map(v => (v === 1 ? '1' : v)).join('');
          note(`Wsig=${wsig.length <= 8 ? wsig : wsig.slice(0, 4) + '..' + wsig.slice(-2)}`);
        }
        note(`Hp: H${H <= 9 ? H : 'Q'} ${p === 0 ? 'p0' : 'p+'}${W.length ? ' W+' : ''}`);
      }
    }
    s = mstepR(s);
    if (!s) { console.log('STUCK', ev); break; }
  }
  console.log(`${boundaries} boundaries; notes/failures: ${bad.length}`);
  for (const b of bad) console.log('  ' + b);
  for (const [k, n] of [...cen].sort((a, b) => b[1] - a[1]).slice(0, 40)) console.log(`  ${n}x ${k}`);
} else if (MODE === '--family') {
  // Boundary states: MC, wall top run exactly 2, rs head >= 4.
  // Hop = mstepR until the next boundary. Inventory hop types.
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  const isBoundary = st => st.m === 'C' && st.wall.length >= 1 && st.wall[0][0] === 1
    && st.wall[0][1] === 2 && st.rs.length >= 1 && st.rs[0] >= 4;
  const rsSketch = rs => {
    // classify: H, then run-length-encoded shape with 1-blocks as P, digits D(v%4), last Q
    const out = [];
    for (let i = 1; i < rs.length - 1; i++) {
      const v = rs[i];
      if (v === 1) { if (out[out.length-1] !== 'P') out.push('P'); }
      else out.push('D' + (v % 4 === 1 ? (v === 5 ? '5' : '9') : '?'));
    }
    return out.join(' ');
  };
  const gsSketch = wall => {
    const out = [];
    for (let i = 1; i < wall.length && out.length < 4; i++) {
      const [v, n] = wall[i];
      if (v === 0) out.push('g' + (n <= 3 ? n : (n % 4 === 3 ? 'B' : n % 4 === 0 ? 'Q' : n % 4)));
      else out.push('r' + (n <= 4 ? n : 'X'));
    }
    if (wall.length > 5) out.push('..');
    return out.join(' ');
  };
  const types = new Map();
  let cur = null, hopStart = 0, ev = 0;
  for (; ev < N; ev++) {
    if (isBoundary(s)) {
      if (cur) {
        const key = cur.cls;
        if (!types.has(key)) types.set(key, { n: 0, hops: [], ex: [] });
        const t = types.get(key);
        t.n++;
        if (t.hops.length < 4) {
          t.hops.push(ev - hopStart);
          t.ex.push(`ev${hopStart}: H=${cur.H} p1=${cur.p1} |gs|=${cur.ngs} -> H'=${s.rs[0]} n=${ev - hopStart}`);
        }
      }
      let p1 = 0; for (let i = 1; i < s.rs.length - 1 && s.rs[i] === 1; i++) p1++;
      const hcls = s.rs[0] === 4 ? '4' : s.rs[0] === 5 ? '5' : s.rs[0] === 9 ? '9' : s.rs[0] % 4 === 0 ? 'Q8' : 'P?';
      cur = { cls: `H${hcls}${p1 === 0 ? 'z' : ''}[${rsSketch(s.rs)}] W[${gsSketch(s.wall)}]`, H: s.rs[0], p1, ngs: s.wall.length - 1 };
      hopStart = ev;
    }
    s = mstepR(s);
    if (!s) { console.log('STUCK at', ev); break; }
  }
  const sorted = [...types].sort((a, b) => b[1].n - a[1].n);
  console.log(`${types.size} hop types over ${ev} events:`);
  for (const [k, t] of sorted.slice(0, 50)) {
    console.log(`${String(t.n).padStart(6)}x ${k}`);
    console.log(`         ${t.ex.join('  |  ')}`);
  }
} else if (MODE === '--rounds') {
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  let printed = 0;
  const rsRle = rs => {
    const out = [];
    for (const v of rs) {
      if (out.length && out[out.length - 1][0] === v) out[out.length - 1][1]++;
      else out.push([v, 1]);
    }
    return out.map(([v, n]) => (n === 1 ? `${v}` : `${v}x${n}`)).join(' ');
  };
  for (let ev = 0; ev < N && printed < 60; ev++) {
    if (s.wall.length <= 2 && s.wall[0][1] <= 2 && s.rs.length > 1) {
      console.log(`ev ${ev} ${s.m} [${wallStr(s.wall)}] rs: ${rsRle(s.rs).slice(0, 150)}`);
      printed++;
    }
    s = mstepR(s);
    if (!s) break;
  }
} else if (MODE === '--filllaw') {
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  let fills = 0, maxRuns = 0;
  const badU = new Map();
  for (let ev = 0; ev < N; ev++) {
    maxRuns = Math.max(maxRuns, s.wall.length);
    if (s.m === 'C' && s.rs.length <= 1) {
      const u = wallT(s.wall) - 1;
      fills++;
      if (u < 1 || u % 4 > 1) badU.set(u, (badU.get(u) ?? 0) + 1);
    }
    s = mstepR(s);
    if (!s) { console.log('STUCK at', ev); break; }
  }
  console.log(`fill law over ${N} events: ${fills} fills, mod-4 violations: ${badU.size === 0 ? 'NONE' : [...badU]}`);
  console.log(`max wall runs: ${maxRuns}`);
} else if (MODE === '--shape') {
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  let maxRuns = 0, maxRs = 0;
  const hist = new Map();
  for (let ev = 0; ev < N; ev++) {
    maxRuns = Math.max(maxRuns, s.wall.length);
    maxRs = Math.max(maxRs, s.rs.length);
    if (ev % Math.max(1, Math.floor(N / 40)) === 0)
      console.log(`ev ${ev}: wallRuns=${s.wall.length} cells=${s.wall.reduce((n, [, l]) => n + l, 0)} rsLen=${s.rs.length}  [${wallStr(s.wall, 14)}]`);
    const sig = s.wall.map(([v, n]) => v).join('');
    hist.set(sig.length, (hist.get(sig.length) ?? 0) + 1);
    s = mstepR(s);
    if (!s) break;
  }
  console.log(`max wall runs=${maxRuns}, max rs len=${maxRs}`);
} else if (MODE === '--probe') {
  let s = { m: 'B', wall: [[1, 1]], rs: [4] };
  for (let ev = 0; ev < N; ev++) {
    leafInfo = null;
    const bad = invbad(s.m, s.wall, s.rs);
    if (bad) {
      console.log(`event ${ev}: ${bad}`);
      console.log(`  state: ${s.m} [${wallStr(s.wall, 20)}] rs=[${s.rs.join(',')}]`);
      if (leafInfo) console.log(`  leaf: ${leafInfo.tag} u=${leafInfo.u} L=${leafInfo.L} w=[${wallStr(leafInfo.w, 20)}]`);
      break;
    }
    s = mstepR(s);
    if (!s) { console.log('stuck'); break; }
  }
} else if (MODE === '--cross') crossCheck(N);
else if (MODE === '--replay') replay(N);
else if (MODE === '--close') closeCheck();
else console.log('modes: --cross N | --replay N | --close');
