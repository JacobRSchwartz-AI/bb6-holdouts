// Generate coq/OdometerNHalt.v: the counted orbit from the blank tape
// to the halt, ending in halts_in tm c0 (N.to_nat N_HALT).
//
// The chain carries no glyph strings of its own. OdometerLedger's 549
// ev_k lemmas already hold them, and leg_c' consumes that exact shape,
// so this file is 549 applications plus one arithmetic total.
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
const repo = dirname(dirname(fileURLToPath(import.meta.url)));

const ICOST = {
  F: { O: 3n, e: 4n, a: 3n, f: 4n },
  A: { O: 8n, e: 7n, a: 11n, f: 4n },
  C: { O: 7n, e: 4n, a: 4n, f: 4n },
  D: { O: 3n, e: 3n, a: 3n },
};
const INSTEP = {
  F: { e: ['e', 'F'], f: ['f', 'A'], O: ['e', 'E'], a: ['f', 'E'] },
  A: { O: ['f', 'C'], f: ['f', 'C'], e: ['a', 'E'], a: ['a', 'E'] },
  C: { a: ['a', 'C'], f: ['f', 'F'], O: ['f', 'E'], e: ['f', 'D'] },
  D: { O: ['e', 'Cr'], a: ['f', 'Cr'], e: ['O', 'Cr'] },
};
const INWARD = new Set(['F', 'A', 'C', 'D']);

function dipCost(W) {
  let s = 'F', deep = [...W], shallow = [], acc = 0n, fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') return acc + 4n * BigInt(shallow.length);
    if (s === 'Cr') { if (shallow[0] !== 'f') return null; acc += 1n; s = 'F'; continue; }
    if (!deep.length) return null;
    const g = deep[0], tr = INSTEP[s]?.[g];
    if (!tr) return null;
    acc += ICOST[s][g];
    const [g2, s2] = tr;
    if (INWARD.has(s2)) { shallow = [g2, ...shallow]; deep = deep.slice(1); s = s2; }
    else { deep = [g2, ...deep.slice(1)]; s = s2; }
  }
  return null;
}
function diesCost(W) {
  let s = 'F', deep = [...W], shallow = [], acc = 0n, fuel = 12 * W.length + 60;
  while (fuel-- > 0) {
    if (s === 'E') return null;
    if (s === 'Cr') { if (shallow[0] !== 'f') return null; acc += 1n; s = 'F'; continue; }
    if (!deep.length) return s === 'C' ? acc + 1n : null;
    const g = deep[0], tr = INSTEP[s]?.[g];
    if (!tr) return null;
    const [g2, s2] = tr;
    if (s2 === 'E') return null;
    acc += ICOST[s][g];
    if (s2 === 'Cr') { deep = [g2, ...deep.slice(1)]; s = 'Cr'; continue; }
    shallow = [g2, ...shallow]; deep = deep.slice(1); s = s2;
  }
  return null;
}

const FPRE = [0n,7n,18n,25n,44n,51n,62n,69n,92n,99n,110n,117n,136n,143n,154n,161n];
const DIGIT = 185n;
function spanBelow(G, v) {
  let acc = 0n;
  for (let g = G; g > 0; g--) { const w = v / 16n; acc += w * DIGIT + FPRE[Number(v % 16n)]; v = w; }
  return acc;
}
const tri = (n) => (n * (n - 1n)) / 2n;
const spancost = (G, v, n, m) =>
  16n * (n * m + tri(n) + n) + 45n * n + (spanBelow(G, v + n) - spanBelow(G, v));
const legcost = (G, v, m, k) => {
  const n = 16n ** BigInt(G) - 1n - v;
  return spancost(G, v, n, m) + (16n * (m + n + 1n) + 25n + k);
};

const GCELLS = ['OOO','fOO','OeO','feO','Oae','fae','Ofe','ffe','OOa','fOa','Oea','fea','Oaf','faf','Off','fff'];
const CV = new Map(GCELLS.map((s, i) => [s, i]));
function parseSpell(W) {
  let G = 0, v = 0n;
  while (2 + 3 * (G + 1) <= W.length) {
    const b = CV.get(W.slice(2 + 3 * G, 2 + 3 * G + 3));
    if (b === undefined) break;
    v += BigInt(b) << BigInt(4 * G); G++;
  }
  return { G, v, T: W.slice(2 + 3 * G) };
}
const spellW = (G, v, T) => {
  let s = 'fO';
  for (let j = 0; j < G; j++) s += GCELLS[Number((v >> BigInt(4 * j)) & 15n)];
  return s + T;
};
const glist = (s) => '[' + [...s].map((c) => 'g' + c).join('; ') + ']';

const { dying, events } = JSON.parse(readFileSync(join(repo, 'data', 'ledger-events.json'), 'utf8'));
const basev = readFileSync(join(repo, 'coq', 'OdometerBase.v'), 'utf8');
const W_BASE = basev.match(/Definition W_BASE : list glyph := \[([^\]]+)\]/)[1]
  .split(';').map((t) => t.trim().replace('g', '')).join('');
const N_BASE = BigInt(basev.match(/Definition N_BASE : nat := (\d+)/)[1]);
const N_TAIL = BigInt(basev.match(/Definition N_TAIL : nat := (\d+)/)[1]);

const starts = [parseSpell(W_BASE)];
for (const e of events) starts.push(parseSpell(e.after));
const fin = starts[events.length];
if (spellW(fin.G, 16n ** BigInt(fin.G) - 1n, fin.T) !== dying)
  throw new Error('final span does not reach the dying string');

// per-leg literals
const legs = [];
let m = N_TAIL;
for (let k = 0; k < events.length; k++) {
  const { G, v, T } = starts[k];
  const cap = 16n ** BigInt(G);
  const kev = dipCost(spellW(G, cap - 1n, T));
  if (kev === null) throw new Error(`leg ${k}: event dip has no cost`);
  legs.push({ G, v, m, k: kev });
  m += cap - v;
}
const capF = 16n ** BigInt(fin.G);
const nF = capF - 1n - fin.v;
const kd = diesCost(dying);
if (kd === null) throw new Error('dying string does not die');

let TOTAL = N_BASE;
for (const L of legs) TOTAL += legcost(L.G, L.v, L.m, L.k);
TOTAL += spancost(fin.G, fin.v, nF, m) + (4n * (m + nF) + 9n + kd);

// segment boundaries: leg indices [start, end) per segment.
// One monolithic Qed hit 2.7GB and swapped; segments bound peak memory.
const SEG = 50;
const segs = [];
for (let a = 0; a < legs.length; a += SEG) segs.push([a, Math.min(a + SEG, legs.length)]);

const closer = `(spancost ${fin.G} ${fin.v} (16 ^ N.of_nat ${fin.G} - 1 - ${fin.v}) ${m}
   + (4 * (${m} + (16 ^ N.of_nat ${fin.G} - 1 - ${fin.v})) + 9 + ${kd}))`;
let nested = closer;
for (let i = segs.length - 1; i >= 0; i--) nested = `SEGCOST_${i}
  + (${nested})`;
nested = `N_BASE_N
  + (${nested})`;

const mAfter = (b) => (b < legs.length ? legs[b].m : m);
const segcost = (a, b) => {
  let e = `legcost ${legs[b-1].G} ${legs[b-1].v} ${legs[b-1].m} ${legs[b-1].k}`;
  for (let j = b - 2; j >= a; j--)
    e = `legcost ${legs[j].G} ${legs[j].v} ${legs[j].m} ${legs[j].k}\n  + (${e})`;
  return e;
};

const L = [];
L.push(`(** * N_halt: the exact number of steps, blank tape to halt.

    GENERATED by tools/gennhalt.mjs -- do not edit by hand.

    N_BASE steps to the base anchor by the bare executor, then ${events.length}
    legs (a counting era plus the event that ends it), then the final
    era and the sweep that dies.

    No glyph strings appear in the legs. OdometerLedger's ev_k lemmas
    already hold them and leg_c' consumes that shape directly.

    The chain is cut into ${segs.length} segments of at most ${SEG} legs. One
    monolithic Qed reached 2.7GB and went to swap; each segment now
    frees at its own Qed. Same fix OdometerOrbit.v needed.

    Every count is a binary N. N_halt has 170 digits and Coq's nat is
    unary, so the index is N.to_nat of it and the kernel never
    normalises it. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerOrbit
                            OdometerCost OdometerSpan OdometerSpanSum
                            OdometerSpanRun OdometerLegCost OdometerDeathCost
                            OdometerBase OdometerHaltIn OdometerLedger.
From Coq Require Import Lia NArith.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope N_scope.
`);

segs.forEach(([a, b], i) => {
  const S = starts[a], E = starts[b];
  const body = [];
  for (let k = a; k < b - 1; k++) {
    body.push(`  eapply multistep_transN.
  { eapply leg_c'.
    - vm_compute. reflexivity.
    - exact ev_${k}.
    - vm_compute. reflexivity. }`);
  }
  body.push(`  eapply leg_c'.
  - vm_compute. reflexivity.
  - exact ev_${b - 1}.
  - vm_compute. reflexivity.`);
  L.push(`Definition SEGCOST_${i} : N :=
  ${segcost(a, b)}.

Lemma seg_${i} :
  anchor (spellW ${S.G} ${S.v} ${glist(S.T)}) (N.to_nat ${legs[a].m})
  -[ tm ]->> (N.to_nat SEGCOST_${i})
  / anchor (spellW ${E.G} ${E.v} ${glist(E.T)}) (N.to_nat ${mAfter(b)}).
Proof.
  unfold SEGCOST_${i}.
${body.join('\n')}
Qed.
`);
});

L.push(`Definition TOTAL : N :=
  ${nested}.

Definition N_HALT : N := ${TOTAL}.

Lemma TOTAL_val : TOTAL = N_HALT.
Proof. vm_compute. reflexivity. Qed.

Theorem odometer_halts_in_TOTAL : halts_in tm c0 (N.to_nat TOTAL).
Proof.
  unfold TOTAL.
  eapply halts_in_prefix. { exact base_reach_cN. }
  replace N_TAIL with (N.to_nat ${N_TAIL}) by reflexivity.
  change W_BASE with (spellW ${starts[0].G} ${starts[0].v} ${glist(starts[0].T)}).
${segs.map((_, i) => `  eapply halts_in_prefix. { exact seg_${i}. }`).join('\n')}
  apply final_c.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** * THE THEOREM. *)
Theorem odometer_halts_in : halts_in tm c0 (N.to_nat N_HALT).
Proof. rewrite <- TOTAL_val. exact odometer_halts_in_TOTAL. Qed.

(** 170 digits: pins the value so a regeneration cannot drift silently. *)
Lemma N_HALT_digits :
  ((10 ^ 169 <=? N_HALT) && (N_HALT <? 10 ^ 170))%bool = true.
Proof. vm_compute. reflexivity. Qed.
`);

writeFileSync(join(repo, 'coq', 'OdometerNHalt.v'), L.join('\n'));
console.log(`wrote coq/OdometerNHalt.v: ${events.length} legs in ${segs.length} segments`);
console.log(`N_HALT = ${TOTAL}`);
