# The Parity machine — formal nonhalt campaign

Machine: `1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA` (BB(6) holdout, frontier
rank #201 by compression, flagged `halt-reached` by the symbolic sieve).
Goal: `Theorem nonhalt : ~ halts tm c0` in busycoq/Coq, zero axioms, CI green.
Chosen 2026-08-18 as the most-likely-provable target from the six-agent
frontier hunt (B1's tier-2 pick; clean arithmetic invariant).

## Rule table, decoded

| state | 0 | 1 | role |
|---|---|---|---|
| A | 1RB | 0LF | left turnaround: A0 writes 1, turns right |
| B | 1RC | 1RB | right scan, preserves 1s, turns at 0 (writes 1) |
| C | 0RD | 0RC | right scan, ERASES 1s, turns at 0 (writes 0) |
| D | 1LE | 1LF | left fill scan (with E), D1 = safe exit |
| E | 1LD | --- | left fill scan; **E1 = HALT — the only halt rule** |
| F | 0LB | 1LA | left halving scan (with A: F keeps 1, A erases to 0); F0 exits to B |

Scan primitives:
- **B-scan**: rightward over 1^k, then B0 writes 1, hands to C.
- **C-scan**: rightward over 1^k erasing all, then C0 writes 0, hands to D.
- **D/E fill scan**: leftward over 0^g writing 1s, alternating D,E,D,E (D first).
  Exits safely via D1 iff g is EVEN. If g is ODD the scan reads the terminating
  1 in state E and HALTS. **The whole nonhalt proof = every fill-scan gap is even.**
- **F/A halving scan**: leftward over 1^k, F preserves, A erases every other one
  (`11` -> `01` per pair). Exits: F0 -> 0LB (to B, rightward); A0 -> 1RB (writes
  1, to B). So the machine bounces between right edge and this left turn.

## Empirical facts (2026-08-18, parity-inv.mjs raw simulation)

- 2×10^8 steps, width 14,759: gaps crossed by fill scan: 23,020,834 of length 0
  (D reads 1 immediately), 12,874 positive — **all even, zero odd**. Max 13,442.
- Positive gap sizes: 2 (5,570×), then exactly the ladder 6, 10, 14, 18, …
  (≡ 2 mod 4), each appearing once per era that reaches it (counts 9,8,7,…
  decreasing with rung height — eras walk the ladder from 6 up to their cap,
  cap grows per era).
- Record fill-scan depth grows +2 per record; no exceptions in 2×10^8 steps
  (nor in B1's independent 2×10^8-step probe).
- C-erase run lengths: overwhelmingly 1 (micro-cycle), then 4,5,8,9,12,16,20,…

## Proof architecture (mirrors the Odometer M4 invariant-closure plan)

1. 2-cell glyph alphabet (the machine's scans are all period-2).
2. Anchor: right-edge configuration entering the fill scan (after C0 at fresh 0).
3. Invariant L: regular grammar over glyphs for the BODY between wall and edge,
   strong enough that every fill-scan gap encountered in one sweep is even.
4. Sweep theorem: anchor(Z∈L) -->+ anchor(Z'∈L) by composed scan lemmas
   (each scan lemma by induction over its glyph run, like Odometer's dip).
5. Close with `progress_nonhalt_cond` (TM.v). Zero axioms; CI job added.

## Predictions registered BEFORE the era-transcript run (protocol)

- P-2026-08-18-a: one era = the fill/halve interplay consumes the `(10)^j`
  region left by halving at rate 4 cells/cycle, gap ladder 6,10,14,… stepping
  +4 per successive deep scan within the era; era ends when the region is
  exhausted, whole 1-block is rebuilt solid and 2 longer, new era's cap +4.
- P-2026-08-18-b: the anchor BODY grammar needs at most 3 glyph letters
  (solid-1 pairs, `10` pairs, and a bounded boundary token) plus one parity
  side condition; no arithmetic ledger (no analog of the Odometer's reservoir
  coupling) will be needed.
- P-2026-08-18-c: no exception events at any scale (unlike the Odometer):
  the machine is genuinely immortal and the era structure is exactly periodic
  in the abstraction — the deep-scan census closes with era index as the only
  unbounded parameter.

## Grades (2026-08-18, after transcript + census runs)

- P-a: **PARTIAL PASS.** Micro-cycles do consume the a-block one glyph per
  cycle into e (fill gap 2 each). The deep event is richer than predicted:
  at a-exhaustion the B/C scan punches through to the right e-block, C erases
  the junction 1 + solid 1s (even total), the fill scan refills the whole
  span (gap = erased + 2, even — the observed deep ladder), and THEN the F/A
  halving converts the left part of the refilled run to a^p and deposits a
  b-marker leftward. Era cap growth mechanics still to be pinned.
- P-b: **FAIL (importantly).** Run-collapse census does NOT close: 19,306
  distinct left-turn patterns at 2e7 steps. The wall between `0^inf` and the
  active zone is a growing recursive token list (observed at successive deep
  A0-turns: `ba.ee|....` -> `ba.ee|.ba.` -> `ba.eea|...` -> `ba.eeaba.` ->
  restructure -> `babee|....`), i.e. a base-2-ish counter of segments, exactly
  the kind of thing a repeated-segment grammar (Kleene over multi-glyph
  tokens) captures but naive run-collapse cannot. Invariant L must be an
  inductive segment grammar (M4-plan style), not a finite pattern union.
- P-c: no exceptions seen yet (consistent); definitive grade deferred.

## THE WALL LAW (B1, 2026-08-18 — the whole invariant)

The wall is a **binary odometer, 4-cell period**: bit k of counter v lives at
single cell r(4k+3) counting from the wall's right edge. Increment (one per
deep turn): R1 no-carry = write 11 at (r3,r4); R2 carry = clear (r3,r4),
recurse at (r7,r8). Verified dv=+1 exactly for 628 consecutive deep A-turns.
Wall grows one 4-cell slot per restructure -> Theta(log T) wall length.

Anchor grammar (cell level): `0^w . W . BLK . 1^L . 0^w`, head on W's last
cell, state A or F reading 0; W = `1 (0+ 1+)* 0^z`; BLK = (10)^p [phase 0] or
(01)^p [phase 1] — phase flips each era, genuine state bit; p>=1, L>=4,
**L = 0 (mod 4)** <- THE invariant; z>=1 (z>=3 except restructure turns).

Exactly THREE fill-scan contexts (2e9 steps, 228,334,570 scans, ZERO odd):
- CTX-0 (g=0, 99.98%): micro-cycle, D reads 1 immediately.
- CTX-2 (g=2): odometer-bit deposit; zeros = {C0 cell, next}; terminator =
  the freshly written bit. Even by construction; needs z>=1.
- CTX-L (g=L+2): punch-through; C erases exactly the L-block; even because
  4 | L; observed ladder 6,10,14,... all = 2 (mod 4).

L transitions: ordinary deep turn L->L+4 (p->p-1); restructure L->L (p->p-1,
wall rebuilt: top 1-run halved INTO the wall, frees a slot); era boundary
L->4, p->L/2+2 (exact, all 11 eras), phase flips. Era length ratio -> 4.0;
width Theta(sqrt T).

Known rough edges (need explicit Coq case-splits, not uniform lemmas):
fixed-slot decode breaks during restructures (slot positions shift while the
top run is halved); z in {1,2} at 20/3836 anchors (all restructure turns).

Coq plan: Inv(phase, W, p, L) := wall_ok W /\ p>=1 /\ L>=4 /\ 4|L; three
sweep lemmas (ordinary/restructure/era-boundary) x three scan contexts.
wall_ok can stay partially opaque: only preservation + z>=1 is needed.
B1's instruments (scratchpad): phases.mjs (per-phase transcript; `node
phases.mjs 14535 14790` = one whole punch/halve cycle), parity1e9.mjs,
scanctx.mjs, restr.mjs, anchors.mjs, rewrite.mjs, odo3.mjs, eras.mjs.

## BOUNDARY TRANSCRIPTS (B1 second pass, 2026-08-18) � CORRECTIONS + exact anatomy

CORRECTIONS to the wall-law section above (B1 second pass supersedes):
1. **No phase bit.** BLK = (1;0)^p uniformly at every deep turn; A-turn head
   = blk-1, F-turn head = blk-2. (In my [0;1]-framed Coq lemmas the r0 cell
   absorbs into the pairs: A faces `0 (10)^p 1^L` = `(01)^p 0 1^L` � same.)
2. **Odometer frame:** r0 = the A-turn cell (fixed within an era), slot k =
   cells (r(4k+3), r(4k+4)); +1 per A->A period, carry depth = ruler fn.
3. **z=4 unreachable.** z=3 <=> slot0 occupied (carry); z>=5(obs >=7) <=> R1.

PHASE MAP (one A->A period): A0 does NOT touch the wall. A-half = launch,
micro train, punch (C-erase L, CTX-L g=L+2), deep halve -> F0 @ r0-1.
**The increment is a single 18-42 step excursion opened by the F0 turn**,
then the F-half runs its own micro train, punch with L'=L+4, halve -> A0.

THE INCREMENT EXCURSION (Coq-ready):
- CS body (9 steps): F0@c, B0@c-1(w1), C0@c(w0), FILL g=2 (D0@c+1, E0@c,
  D1@c-1) -> head F@c-2, cells c-1,c,c+1 all 1. As a stream lemma:
  `l <* <[0;0] <{{F}} 0 >> r -->* l <{{F}} 1 >> 1 >> 1 >> r`  (execute).
- Dispatch on tape[c-2]: 0 => R1 tail (B0 sets r4, micro-ish shuffle, B0
  sets r3, C-erase(4) over the 3 CS-ones + first pair 1, C0 at pair 0,
  D1 safe) -> micro train. 1 with run exactly 2 => carry: HALVE(2) =
  FA_halve n=1 (3 steps), recurse at c-4. 1 with run >=3 => RESTRUCTURE.
- R2 depth-1 verified step-exact (s9168-9197): clear of r4 = the A1 erase
  inside HALVE(2); clear of r3 = the terminal C-erase; set of r8,r7 = two
  B0 writes. Depth-d = d x HALVE(2) interleaved with (d+1) x CTX-2.
  OPEN: s11444 depth-2-into-base variant shows one FEWER CTX-2 - third
  sub-case needing its own transcript before the general R2 lemma.

R1 INSTANCE (s8012->s8603): `<[1;1;0^8] {{F}}> [0^2;(1;0)^45;1^16]` ->
  `<[1;1;0^5;1;1;0^2] {{A}}> [0;(1;0)^44;1^20]` (p-1, L+4, slot0 set).
**B1 CORRECTION (second pass): the landing-cell dispatch is FOUR-way,
keyed on tape[c-1] FIRST** (149/149 agreement to s400000):
- (D) tape[c-1]=1 -> DEGENERATE CS: B preserves that 1 and turns one cell
  RIGHT, so C0 lands at c+1, D starts at c+2 = the low cell HALVE(2) left
  set, reads 1 -> gap 0 (CTX-0, not CTX-2). Leaf case, no recursion;
  terminal C-erase is 4d+1, not 4d+4. Fires when the carry chain runs out
  of lattice-aligned slots and meets a base run sitting +1 off-lattice
  (v = 2^m - 1 mod 2^m); one-shot per wall layout (it fuses the pair into
  the base and re-aligns). Two instances to s400000: s11444, s147336.
- (A) tape[c-1]=0, tape[c-2]=0 -> R1 set, excursion ends.
- (B) tape[c-1]=0, run at c-2 = 2 -> HALVE(2), recurse at c-4.
- (C) tape[c-1]=0, run at c-2 = n>=3 -> RESTRUCTURE, split on n mod 2.
  **n odd -> exits A0 (base extends 1 cell left, 3 refills); n even ->
  exits F0 (base jumps 4 cells left, 5 refills).** 33/33 exact.
NOTE: the earlier line "depth-d = d x HALVE(2) + (d+1) x CTX-2" is WRONG in
the degenerate case; and the even-restructure exit figure is 0^10 at event
exit (0^8 only later at the next A-anchor).
UNIFIED POST-CONDITION (all three wall-cascade sub-cases):
`const 0 <* <[BASE; 0^9] {{F}}> [0; (1;0)^^(p-1); 1^^L]`, L unchanged, one
pair consumed; only BASE differs (anomaly 1^4; odd 1^5; even 1^2 0^3 1^4).
Fill audits inside all windows: 9/5/5 fills, gaps in {0,2}, all exit D1.
Fresh 2e7-step global run: 2,498,993 fills, ZERO odd.

R2 INSTANCE (s9168->s9763): `<[1;1;0^5;1;1;0] {{F}}> [0^2;(1;0)^43;1^24]` ->
  `<[1;1;0;1;1;0^6] {{A}}> [0;(1;0)^42;1^28]` (slot0->slot1).

RESTRUCTURE (odd base, s15804->s16363): CS, HALVE(2) carry, CS, then head
meets base 1^5 (run>=3): HALVE(5) runs THROUGH it, A0@-33 = the extra deep
turn extends base one cell LEFT; 3 B0 refill writes rebuild base solid
1 cell left; freed cell = one new slot; then normal half-period. Net:
base 1^5 shifts left 1, counter zone 0^7 -> 0^8, p-1, L+4.
**Even-base sub-case differs** (s19916, base 1^6: exits F0, leftmost 1
jumps 4 cells, longer tail) - budget a separate lemma; needs transcript.

ERA BOUNDARY (s5913->s6311, p=1): R1 increment; last 2 micros; punch
C-erase(88=L); CTX-L g=90; SHALLOW A-turn (halve meets wall after 1 one);
tape = solid 1^(L+8); B-scan right, B0 writes at right edge; an extra
CTX-2 AT THE RIGHT EDGE (same lemma, different neighborhood); HALVE(L+5)
keeps/erases alternately -> A0. p' = (L+8-4)/2 = L/2+2 exact; L' = 4.

B1 instruments (scratchpad): dt2.mjs (deep-turn configs in busycoq
notation), walldiff.mjs (absolute-aligned wall cells - cracked the slot
geometry), wtrace.mjs (per-state-run transcript with wall window),
period.mjs (per-interval anatomy), dt_all.txt (278 deep turns to 300k).

## Coq progress (coq/Parity.v, all GREEN in WSL against busycoq upstream)

Atoms: B_ones, C_ones, DE_fill (D-first even fill), ED_fill (E-first),
FA_halve. Phases: B_phase, C_phase, D_phase, F_exit_even, F_exit_odd.
Micro: micro_step (10-step pair shuffle, verified by execute), micro_all
(induction over the pair region). Glue: launch_entry (A-turn -> micro
anchor, 6 steps), junction (last 2 pairs -> C at block face, deposits 1^6),
punch_refill (C erase 2m + fill: `l <* <[1] {{C}}> [1]^^(2m) *> const 0
-->* l <{{F}} 1 >> 1 >> [1;1]^^m *> 1 >> const 0`), ones_comm, lpow_pair.
Startup: c0 --> first structured config (8 steps).

**incr_full (GREEN) � the odometer increment at ANY carry depth, one lemma:**
`l <* <[0;0] <* ([1;1] ++ [0;0])^^d <* <[0;0] <{{F}} 0 >> [1;0] *> [1;0] *> [1] *> r
 -->* l <* <[1;1] <* [0]^^(4*d+4) {{F}}> [0;1;0;1] *> r`
d occupied lattice slots cleared, slot d set, zero field ends 4d+4 wide.
Built from cs_body (9 steps, the CTX-2 fill), carry_step (= FA_halve 1),
excursion_chain (induction on d � this is where the 4-cell pitch is
DERIVED), bitset, C_phase. Verified vs simulator: d=0 -> s8031, d=1 -> s9199.
The hypothesis shape (lattice-aligned [0;0] gaps) is exactly what excludes
B1's degenerate case, so this lemma is sound as stated.

**sweep_F (GREEN)** � the F-half period from the micro anchor the increment
hands over, through micros/junction/punch/refill/halve to the wall face.

**half_period (GREEN) � THE INVARIANT STEP:**
`l {{A}}> [0;1]^^(k+5) *> [0] *> [1]^^(2*m+2) *> const 0 -->*
 l <{{F}} [0;1]^^(k+4) *> [0] *> [1]^^(2*m+6) *> const 0`
One half period consumes exactly ONE pair and grows the block by exactly
FOUR. Block enters 2m+2, leaves 2m+6: evenness preserved, which is
precisely punch_refill's hypothesis (the fill scan crosses an even gap and
exits in D, never in E). `p -> p-1, L -> L+4` is now a theorem, not a
census. Helper: tail_regroup (refold the solid block).

**half_period_4 / half_period_2 (GREEN)** � the last turns of an era have
fewer than five pairs. p=4: launch hands straight to the junction, no
micro train. p=2: launch runs into the block; p2_glue (7 steps) puts C on
its face. Both land the same recurrence (one pair consumed, block +4).

**era_incr (GREEN)** � at p=1 the increment's terminal erase runs out of
pairs, so C ends on the face of the block, not at a micro anchor. 26
concrete steps, read off the raw trace at s778.

**era_boundary (GREEN) � THE UNBOUNDEDNESS:**
`l <* <[0;0] <* <[0;0] <{{F}} 0 >> [1;0] *> [1]^^(2*M+2) *> const 0 -->*
 l <* <[1;1] <* <[0] {{A}}> [0;1]^^(M+3) *> [0] *> [1]^^4 *> const 0`
Block consumed whole, tape becomes one solid run, halving it back rebuilds
the pair region. **p' = M+3 = L/2+2 and L' = 4 are DERIVED**, not fitted:
the run is 2M+7 (odd), so the halve yields M+3 pairs and the leftover 1
feeds the A-turn. Helpers: shallow_A, right_edge (the right-edge CTX-2),
f1_to_A, ones_succ'. This is what stops p running down -- without it the
invariant is not closed and the orbit is only finitely long.

**sweep_A_odd (GREEN, the full A-type half-period):**
`l <* <[0] <* <[1] {{A}}> [0;1]^^(k+5) *> [0] *> [1]^^(2*m+2) *> const 0
 -->* l <* <[1] {{B}}> 1 >> [0;1]^^(k+5) *> [1] *> [1] *> [1;1]^^(m+1) *> [1] *> const 0`
The wall-top `0 1` under the anchor is the low bit-pair: the halving run
swallows its top 1 (making the run odd) and the A0-write of F_exit_odd IS
the odometer bit write. KEY INSIGHT from composing forward: the RHS block
is FUSED to the pairs (no 0 separator), so the NEXT half-period (F-type)
has a different junction anatomy: micros run pairs directly against 1s,
the B0-filled junction makes the C-erase even, refill re-creates the
separator, p drops there. A-half and F-half alternate and need separate
junction/punch lemmas; B1's phase map + transcripts pin the F-half.

**sweep_core (GREEN, the half-period workhorse):**
`l {{A}}> [0;1]^^(k+5) *> [0] *> [1]^^(2*m+2) *> const 0 -->*
 l <{{F}} [0;1]^^(k+5) *> [1] *> [1] *> [1;1]^^(m+1) *> [1] *> const 0`
i.e. from a deep A-turn: launch (2 pairs net), micro_all, junction, punch,
even refill, halving — F arrives at the wall face; pair count preserved
at this granularity (the p-decrease happens in the wall phase), block grown.
Proof pattern that works: peel literal pairs with lpow_add/Str_app_assoc +
lpow_shift', let `follow` unify up to conversion (no bare-list `change` —
list literals outside a `*>` context fail scope resolution), and note that
each `follow X.` runs finish's autorewrite which JOINS all-ones runs —
probe goals with coqtop `Show` before writing normalization steps.
Debug loop: `awk "NR<=N" Parity.v > ParityDbg.v; echo "Show. Abort." >>;
coqtop -batch -load-vernac-source` prints the exact goal at line N.
Compile: `wsl cp coq/Parity.v ~/busycoq/verify/ && coqc -Q . BusyCoq Parity.v`
(~20s; Individual62 chain already .vo-cached in ~/busycoq/verify).

## Decoded event anatomy (window s20195-s20479, era at width ~90)

1. Micro-cycle (~10 steps): `B0R C0R D1L F0L` variants at the e/a boundary;
   fill gaps are the aligned `.` glyph (gap 2, even).
2. Punch-through: `C1R^104` (junction 1 + e-block, even), right edge +2,
   `D/E fill ^106` (even, the ladder event), exit D1 at the junction.
3. Deep halving: `F1/A1` alternating over the refilled 1-run (45 ones),
   `A0R` turn at the left; halved region becomes the new a-block, b-marker
   deposited, one dot of the left gap consumed.
4. Wall cascade: when the dot-gap exhausts, the wall's own e-segment gets
   halved and restructured (`ba.ee` -> `babee`), dots replenished — the same
   dynamic one level up, self-similar.

## STATE 2026-08-18 (47 lemmas, all `Closed under the global context`)

PROVEN, covering the orbit end to end except the wall's own bookkeeping:
- half_period / half_period_4 / half_period_2 : the A-turn half period for
  every even pair count. p -> p-1, L -> L+4, EVENNESS PRESERVED (the whole
  halt-guard argument).
- incr_full : the odometer increment at every carry depth (R1 + R2 in one).
- f_to_a : the F-turn half period WITH its wall write (increment excursion,
  micro train, punch, halve) -> next A-turn, wall incremented.
- era_incr_d / era_boundary_d : the era reset at every carry depth.
  p' = M+3 = L/2+2 and L' = 4 DERIVED (run length 2M+7 is odd, so the halve
  yields M+3 pairs and the leftover 1 feeds the A-turn).
- degen_cs : B1's fourth dispatch branch (tape[c-1]=1), which is exactly
  what fires at the FIRST F-turn of a new era -- confirmed on the machine
  at s1173, five steps, no carry.

THE REMAINING GAP, stated precisely.
The wall alignment shifts by one cell across an era boundary:
era_boundary_d leaves the A-turn with `[0]^^(4d+1) ++ [1;1] ++ l`, one zero
short of the `[0;0] ++ (1100)^d ++ [0;0] ++ l` shape that f_to_a needs. That
is not a bug -- it is why degen_cs exists and why B1 saw the fixed-slot
decode drift. So closure needs:
1. degen_cs composed forward into a full era-start F-turn -> A-turn lemma
   (the micro train after it does NOT match micro_all as stated: the cell
   left of the anchor is 1, not 0 -- needs its own short induction).
2. `slots : list bool -> list Sym` (4 cells/slot, [1;1;0;0] set,
   [0;0;0;0] clear) + `slots_decomp` (every counter has a lowest clear
   slot; base case needs Helper.const_unfold via a blank_app lemma).
   f_to_a then reads: wall = [0;0] *> slots bs *> const 0, and its output
   is [0;0] *> slots (bump bs) *> const 0. I verified this identity by
   hand; it is the reason the wall closure works at all.
3. An induction over the (even) pair count p: half_period* then f_to_a,
   down to p=2, then era_boundary_d. Gives A-turn(era k) -->+ A-turn(era k+1).
4. progress_nonhalt_cond with C = the A-turn anchor and the index
   (bs, p, m); base case from `startup`. Then the CI job.

The restructure sub-cases (odd/even base) are NOT needed for 1-4: they are
what keeps the counter's own representation finite over very long runs, and
the invariant in (2) admits them as further `slots` values. Their exact
transcripts are above if they turn out to be needed.

## RETRACTION + CORRECTED FINDING (2026-08-18, settled by exact parse)

I earlier called the era-start case an "obstacle" and said a clean
(wall | pairs) split "cannot close". **That was wrong, and it is retracted.**

What settled it: `anchor2.mjs` parses each deep turn by locating the BLOCK
first (maximal 1-run at the right end) and then requiring the cells between
head and block to be exactly `[0;1]^^P ++ [0]`. No RLE eyeballing, no
heuristic. It parses every deep turn exactly. Results:

  s952  A P=18 L=4    left=0110011
  s1173 F P=17 L=8    left=110011
  s1408 A P=18 L=12   left=011
  s1645 F P=17 L=16   left=11
  s1896 A P=18 L=20   left=(blank)

  s129 A P=6 L=4 | s206 F P=5 L=8 | s297 A P=6 L=12 | s390 F P=5 L=16
  s501 A P=4 L=20 | s586 F P=3 L=24 | s701 A P=2 L=28 | s778 F P=1 L=32

So P genuinely oscillates and L grows by exactly 4 at EVERY deep turn.
**L, not P, is the monotone quantity**, and the halt guard only ever needs
L even. My derivation of P -> P+1 for the era start was correct; my
expectation that P must decrease was the error.

`f_to_a_era` is now PROVEN with exactly that statement (P -> P+1,
L -> L+4), matching s1173 -> s1408 (17 -> 18, 8 -> 12) on the nose.

WHICH F-HALF LEMMA APPLIES, keyed on the left string (nearest head first),
checked against every deep turn above:
  left starts 0,0,0,0.....  -> f_to_a, d=0        (s390, blank left)
  left starts 0,0,(1100)^d  -> f_to_a, depth d    (s586: 0,0,1,1,0,0)
  left starts 0,1,1,0,0     -> f_to_a_era         (s206, s1173, s1645)
  p = 1                     -> era_boundary_d     (s778)
All four are proven. The A-half (half_period / _4 / _2) is left-generic and
covers every even P.

WHAT REMAINS is only the wall induction: showing the four cases above are
jointly closed, i.e. that the left string after each step is again one of
these shapes. The observed wall cycle is
  0110011 -> 110011 -> 011 -> 11 -> (blank) -> regrow,
which is the odometer counting up while the halvings eat it back down.
This is a `slots`-style induction over the counter, not new machine analysis.

## COVERAGE TEST (tools/parity-cover.mjs) -- what is actually still missing

At every deep turn, decide which PROVEN lemma applies by pattern-matching
the wall and the right side. Over 2e7 steps:

  1087  half_period            390  f_to_a(d=0)        5  f_to_a_era
     8  half_period_2            4  f_to_a(d=1)        4  era_boundary_d(d=0)
     7  half_period_4            2  f_to_a(d=2,3)
   ~730  F-UNCOVERED (30 distinct wall prefixes)
    288  RIGHT-UNPARSED
      4  BOUNDARY-UNCOVERED

So roughly two thirds of deep turns ARE covered by proven lemmas and one
third is not. The uncovered walls are exactly the restructure family, and
the reason is visible in the prefixes:

  001100011000   00 | 1100 | 0 | 11 | 000      <- an EXTRA zero before the
  000110000000   000 | 11 | 0000000               next slot; pitch is not 4
  001111000000   00 | 1111 | 000000             <- a FOUR-one run, not a slot

My `slots` model assumes a uniform 4-cell pitch with slots [1;1;0;0]. That
is exactly right in the ordinary regime (it reproduces the tape at v=0,1,2
and classA_step/classB_step are proven against it), but restructures shift
a run one cell left and merge runs, so the pitch drifts and runs of four
ones appear. This is precisely what B1 flagged: "the fixed-slot decode
breaks in the last ~6% of each era, exactly at the restructures", and
"those shift a run 1 cell left, turning its gap 0^3 -> 0^2 -> 0^1".

I previously wrote that the restructure sub-cases were NOT needed for
closure. **That was wrong.** They are needed, they are about a third of all
deep turns, and B1's step-exact transcripts for both (odd base s15804,
even base s19916) are in this file waiting to be turned into lemmas.

REMAINING, now precisely scoped and measurable:
1. odd-base restructure lemma (base 1^n, n odd: exits A0, base +1 cell,
   3 refill B0 writes) -- transcript above.
2. even-base restructure lemma (n even: exits F0, base +4 cells, 5 refills)
   -- transcript above.
3. generalise `slots` to a variable-pitch wall admitting the shifted runs
   (or carry an explicit per-slot offset).
4. the RIGHT-UNPARSED turns (288) -- inspect; likely mid-restructure
   anchors where the right side is not yet the clean [0;1]^^P form.
5. then the P descent induction and progress_nonhalt_cond.

Run `node tools/parity-cover.mjs 20000000` after each new lemma; the
uncovered count is the honest progress metric.
