// Closure model-checker for the parity machine's run-level invariant.
//
// Mirrors coq/Parity.v EXACTLY: exc / mstep transcribed literally (list form),
// plus an RLE twin for fast orbit replay. The candidate invariant invb is
// developed here first; only a JS-closed invariant gets encoded in Coq.
//
//   node parity-close.mjs --cross 200000     RLE mstep == list mstep on orbit
//   node parity-close.mjs --replay 30000000  orbit census: invb at every state
//   node parity-close.mjs --close            synthetic closure: Inv -> Inv
//
// Wall lists are top-first arrays of 0/1 (Coq: list Sym, ws *> const 0).
// RLE walls are arrays of [sym, len], top-first. rs is an array of nats.

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

if (MODE === '--roundtrace') {
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
