# The Parity machine â€” formal nonhalt campaign

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
| E | 1LD | --- | left fill scan; **E1 = HALT â€” the only halt rule** |
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

- 2Ã—10^8 steps, width 14,759: gaps crossed by fill scan: 23,020,834 of length 0
  (D reads 1 immediately), 12,874 positive â€” **all even, zero odd**. Max 13,442.
- Positive gap sizes: 2 (5,570Ã—), then exactly the ladder 6, 10, 14, 18, â€¦
  (â‰¡ 2 mod 4), each appearing once per era that reaches it (counts 9,8,7,â€¦
  decreasing with rung height â€” eras walk the ladder from 6 up to their cap,
  cap grows per era).
- Record fill-scan depth grows +2 per record; no exceptions in 2Ã—10^8 steps
  (nor in B1's independent 2Ã—10^8-step probe).
- C-erase run lengths: overwhelmingly 1 (micro-cycle), then 4,5,8,9,12,16,20,â€¦

## Proof architecture (mirrors the Odometer M4 invariant-closure plan)

1. 2-cell glyph alphabet (the machine's scans are all period-2).
2. Anchor: right-edge configuration entering the fill scan (after C0 at fresh 0).
3. Invariant L: regular grammar over glyphs for the BODY between wall and edge,
   strong enough that every fill-scan gap encountered in one sweep is even.
4. Sweep theorem: anchor(ZâˆˆL) -->+ anchor(Z'âˆˆL) by composed scan lemmas
   (each scan lemma by induction over its glyph run, like Odometer's dip).
5. Close with `progress_nonhalt_cond` (TM.v). Zero axioms; CI job added.

## Predictions registered BEFORE the era-transcript run (protocol)

- P-2026-08-18-a: one era = the fill/halve interplay consumes the `(10)^j`
  region left by halving at rate 4 cells/cycle, gap ladder 6,10,14,â€¦ stepping
  +4 per successive deep scan within the era; era ends when the region is
  exhausted, whole 1-block is rebuilt solid and 2 longer, new era's cap +4.
- P-2026-08-18-b: the anchor BODY grammar needs at most 3 glyph letters
  (solid-1 pairs, `10` pairs, and a bounded boundary token) plus one parity
  side condition; no arithmetic ledger (no analog of the Odometer's reservoir
  coupling) will be needed.
- P-2026-08-18-c: no exception events at any scale (unlike the Odometer):
  the machine is genuinely immortal and the era structure is exactly periodic
  in the abstraction â€” the deep-scan census closes with era index as the only
  unbounded parameter.

## Grades (2026-08-18, after transcript + census runs)

- P-a: **PARTIAL PASS.** Micro-cycles do consume the a-block one glyph per
  cycle into e (fill gap 2 each). The deep event is richer than predicted:
  at a-exhaustion the B/C scan punches through to the right e-block, C erases
  the junction 1 + solid 1s (even total), the fill scan refills the whole
  span (gap = erased + 2, even â€” the observed deep ladder), and THEN the F/A
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

## THE WALL LAW (B1, 2026-08-18 â€” the whole invariant)

The wall is a **binary odometer, 4-cell period**: bit k of counter v lives at
single cell r(4k+3) counting from the wall's right edge. Increment (one per
deep turn): R1 no-carry = write 11 at (r3,r4); R2 carry = clear (r3,r4),
recurse at (r7,r8). Verified dv=+1 exactly for 628 consecutive deep A-turns.
Wall grows one 4-cell slot per restructure -> Theta(log T) wall length.

Anchor grammar (cell level): `0^w . W . BLK . 1^L . 0^w`, head on W's last
cell, state A or F reading 0; W = `1 (0+ 1+)* 0^z`; BLK = (10)^p [phase 0] or
(01)^p [phase 1] â€” phase flips each era, genuine state bit; p>=1, L>=4,
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

## BOUNDARY TRANSCRIPTS (B1 second pass, 2026-08-18) — CORRECTIONS + exact anatomy

CORRECTIONS to the wall-law section above (B1 second pass supersedes):
1. **No phase bit.** BLK = (1;0)^p uniformly at every deep turn; A-turn head
   = blk-1, F-turn head = blk-2. (In my [0;1]-framed Coq lemmas the r0 cell
   absorbs into the pairs: A faces `0 (10)^p 1^L` = `(01)^p 0 1^L` — same.)
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

**incr_full (GREEN) — the odometer increment at ANY carry depth, one lemma:**
`l <* <[0;0] <* ([1;1] ++ [0;0])^^d <* <[0;0] <{{F}} 0 >> [1;0] *> [1;0] *> [1] *> r
 -->* l <* <[1;1] <* [0]^^(4*d+4) {{F}}> [0;1;0;1] *> r`
d occupied lattice slots cleared, slot d set, zero field ends 4d+4 wide.
Built from cs_body (9 steps, the CTX-2 fill), carry_step (= FA_halve 1),
excursion_chain (induction on d — this is where the 4-cell pitch is
DERIVED), bitset, C_phase. Verified vs simulator: d=0 -> s8031, d=1 -> s9199.
The hypothesis shape (lattice-aligned [0;0] gaps) is exactly what excludes
B1's degenerate case, so this lemma is sound as stated.

**sweep_F (GREEN)** — the F-half period from the micro anchor the increment
hands over, through micros/junction/punch/refill/halve to the wall face.

**half_period (GREEN) — THE INVARIANT STEP:**
`l {{A}}> [0;1]^^(k+5) *> [0] *> [1]^^(2*m+2) *> const 0 -->*
 l <{{F}} [0;1]^^(k+4) *> [0] *> [1]^^(2*m+6) *> const 0`
One half period consumes exactly ONE pair and grows the block by exactly
FOUR. Block enters 2m+2, leaves 2m+6: evenness preserved, which is
precisely punch_refill's hypothesis (the fill scan crosses an even gap and
exits in D, never in E). `p -> p-1, L -> L+4` is now a theorem, not a
census. Helper: tail_regroup (refold the solid block).

**half_period_4 / half_period_2 (GREEN)** — the last turns of an era have
fewer than five pairs. p=4: launch hands straight to the junction, no
micro train. p=2: launch runs into the block; p2_glue (7 steps) puts C on
its face. Both land the same recurrence (one pair consumed, block +4).

**era_incr (GREEN)** — at p=1 the increment's terminal erase runs out of
pairs, so C ends on the face of the block, not at a micro anchor. 26
concrete steps, read off the raw trace at s778.

**era_boundary (GREEN) — THE UNBOUNDEDNESS:**
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
even refill, halving â€” F arrives at the wall face; pair count preserved
at this granularity (the p-decrease happens in the wall phase), block grown.
Proof pattern that works: peel literal pairs with lpow_add/Str_app_assoc +
lpow_shift', let `follow` unify up to conversion (no bare-list `change` â€”
list literals outside a `*>` context fail scope resolution), and note that
each `follow X.` runs finish's autorewrite which JOINS all-ones runs â€”
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
   halved and restructured (`ba.ee` -> `babee`), dots replenished â€” the same
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

## COVERAGE AFTER THE RESTRUCTURES (2026-08-18, final measurement)

  1851 / 2492 deep turns covered by proven lemmas = 74.3%

  1087 half_period     390 f_to_a(d=0)      172 restructure_odd
     8 half_period_2     6 f_to_a(d=1,2,3)  172 restructure_even
     7 half_period_4     5 f_to_a_era         4 era_boundary_d
   349 F-UNCOVERED     288 RIGHT-UNPARSED     4 BOUNDARY-UNCOVERED

The restructures took the gap from 730 to 349, as predicted. What is left
is a DIFFERENT thing, and it is worth naming precisely because it is the
real remaining research content:

  001100011000   00 | 1100 | 0 | 11 | 000    gap of ONE zero between slots
  000110000000   000 | 11 | 0000000          first slot at offset THREE

Every lemma I have (cs_body, excursion_chain, incr_full) assumes the wall
is `[0;0] ++ (1100)^d ++ [0;0]`: first slot at offset 2, gaps of exactly 2.
These walls have offset 3 and gaps of 1. So the wall is NOT a uniform
4-cell-pitch odometer in general -- the pitch varies, which is the deeper
form of the same drift the restructures cause.

Mechanically what happens on such a wall: cs_body still fires (it only
needs two zeros), the head emerges two cells left, and THEN the dispatch
finds a 1 where the clean model expects a 0 -- i.e. it lands in the
degenerate branch (degen_cs, proven) rather than the carry branch. So the
pieces exist; what is missing is a general excursion lemma that dispatches
on the wall cell by cell with a well-founded induction, instead of
excursion_chain's fixed (1100)^d pattern.

HONEST ASSESSMENT. That generalisation is the remaining work and it is not
a rewrite of existing lemmas -- it is a new induction over an alphabet of
wall shapes I have not characterised. I do not have a proof that the
reachable wall language is finitely describable, and B1's data (30 distinct
prefixes at 2e7 steps, still growing) does not settle it either way. This
is the honest boundary of the campaign as of this session.

WHAT IS SOLID: the parity core is complete and unconditional. Every fill
scan in every proven lemma crosses an even gap, and the only halt rule is
E reading 1. `half_period` shows one half period preserves block evenness
with no side conditions at all. If the wall induction is completed, the
non-halt theorem follows from what is already proven.

## THE RESEARCH STEP: characterising the wall language (tools/parity-walllang.mjs)

Census over 2e7 steps, at every deep F-turn, of the wall as a run sequence:

  deep F-turns sampled: 1306
  DISTINCT WALL SHAPES: 1244            <- essentially all different
  leading 0-run:  1:10  2:645  3:188  5:1  6:227  7:223  9:1  10:2  14:1
  all 0-runs:     1,2,3,4,5,6,7,8,9,10,11,14
  all 1-runs:     2,3,4,5,6,7,8,9,10,11,12,20,21,22

READ THIS CAREFULLY, IT REDIRECTS THE PROOF.

1. The wall shape almost never repeats (1244/1306). There is NO finite set
   of wall shapes to enumerate, so the plan of "characterise the reachable
   wall language and case-split on it" is a dead end. My uniform 4-cell
   odometer was a special case that happens to hold in the clean regime.
2. But the RUN LENGTHS are small and slow-growing: gaps 1..14, slot runs
   2..12 plus a growing base run (20,21,22 are the base). So the wall is a
   long word over a small run alphabet, not an arbitrary string.
3. Crucially, the wall is always a FINITE prefix followed by blank tape.

=> THE RIGHT FORMULATION IS A GENERAL EXCURSION LEMMA, NOT A WALL GRAMMAR.

Do not try to say which walls occur. Prove instead: for ANY left stream of
the form `ws *> const 0` (ws finite), the increment excursion terminates
and reaches the next deep turn. This is true for a structural reason that
needs no census at all -- the excursion walks LEFT, and beyond ws the tape
is all zeros, so the R1 no-carry branch (which needs only two adjacent
zeros with a zero beyond) must eventually fire. Termination is a
well-founded induction on ws.

The pieces are already proven and left-generic in exactly the needed way:
  cs_body      consumes two wall zeros, head 2 cells left
  carry_step   consumes an occupied slot (erases a 1), head 4 cells left
  degen_cs     the tape[c-1]=1 branch
  bitset       the terminating write
What is missing is only the dispatcher: a fixpoint over ws choosing among
these four, plus its termination measure. That is ordinary Coq work over a
finite list, NOT new machine analysis and NOT a wall grammar.

This is the single most useful thing this session produced for finishing
the proof, and it only became visible by measuring instead of assuming.

## THE HALT CRITERION, AT RUN LEVEL (this is the reduction that matters)

Stripped of all context the machine is a four-phase cycle and nothing else:

  B  scan right over 1s to the first 0, write it, hand to C
  C  scan right over the NEXT 1-run, erasing, to the following 0, hand to D
  D/E fill that zero field LEFTWARD, alternating D,E,D,E starting in D
  F/A halve leftward over 1s (`11` -> `01`), exit at a 0

Only the fill can halt, and only by reading a 1 in state E. Count its
alternation. Let the tape from B's entry read `1^a 0^b 1^c 0^d ..`. The
fill starts one cell past the 0 that C stopped on, so:

  d = 1  -> it meets a 1 immediately. SAFE whatever c is.
  d >= 2 -> it crosses c + 2 cells before reaching the 1 that B wrote.
            SAFE iff c is EVEN.

  ==> THE MACHINE HALTS IFF SOME C-SCAN ERASES AN ODD RUN OF 1s THAT IS
      FOLLOWED BY A ZERO-RUN OF LENGTH TWO OR MORE.

Both branches are now theorems: `macro_gap0` and `macro_fill`, for
arbitrary a, c, n and arbitrary context on BOTH sides. `macro_fill`
generalises `punch_refill`, which needed blank tape past the block, so the
criterion applies to right sides carrying more than one block -- exactly
the family the standard parse had been rejecting.

MEASURED (parity-cover.mjs, 2e7 steps): of the 2,498,993 fill scans the
machine performs, 2,495,023 are gap 0 (`macro_gap0`) and 3,970 are even
gap (`macro_fill`). ODD gaps: ZERO. Every fill the machine has ever
performed is discharged by one of two general proven lemmas.

Also measured (parity-fill.mjs): every one of those even gaps is not just
even but 2 mod 4, i.e. every erased block has length divisible by four --
consistent with `half_period`'s L -> L+4 and the era boundary's L' = 4.

### The shortcut that does NOT work (negative result, tools/parity-inv.mjs)

The obvious hope is that "odd 1-run followed by two or more 0s" is simply
absent from the tape, giving a local invariant provable by case analysis
on the twelve transitions. It is not. Over 2e6 steps the tape carries such
a run at essentially every configuration -- 324,895 of them at or right of
the head. The runs exist; what never happens is that C *enters* one in the
erasing phase. So the invariant has to be about reachable configurations,
not about the tape alone. That kills the cheap route, and it was worth one
tool to find out rather than several sessions.

## THE GENERAL EXCURSION IS DONE (was "the one remaining piece")

The wall-language census had ruled out enumerating the reachable walls.
`excursion_gen` proves the leftward walk instead for an ARBITRARY finite
wall, by induction on a bound for its length. Two right-hand phases (the
head faces `0 1 ..` or `1 ..`) times four (head cell, next cell) shapes is
eight branches, and every one is an atom that was already proved:

  phase  head,next   atom          effect
  P0     0,0         cs_body       -> P1, two wall cells consumed
  P0     0,1         degen_cs      terminates, F facing right
  P0     1,0         f1_to_A       terminates, A-turn
  P0     1,1         carry_step    -> P0, two wall cells consumed
  P1     0,0         bitset        terminates, C facing right
  P1     0,1         bitset_odd    terminates, C facing right  (NEW, 3 steps)
  P1     1,0         f1_to_A       terminates, A-turn
  P1     1,1         carry_step    -> P0, two wall cells consumed

Only the carry and the CS body continue leftward and each eats two cells,
so the walk terminates; past the wall the tape is blank, where it is
cs_body then the bit write. The excursion therefore NEVER HALTS, whatever
the wall -- the left half of the machine is unconditionally safe.

## THE RUN-LEVEL MACHINE IS FORMAL (2026-08-20)

tools/parity-macro.mjs implements the machine as a run-level abstract
system: wall = cell list over blank, right side = list of 1-run lengths
separated by single 0s (a cap bit marks the P0 form). CO-VERIFIED against
the raw simulator at every one of 2,498,992 fill exits over 2e7 steps,
byte-exact, and the gap0/fill tallies cross-check parity-cover exactly
(2,495,023 + 3,970). The events: BE (B skims the leading run), CE (C
erases it -- d=1 nibble safe for any run, d>=2 fill NEEDS EVEN), EXC
(the excursion dispatch: carry pushes 01, cs pushes 111 eating the cap,
bitset/bitset_odd/degen exit to CE, f1_to_A exits to BE).

MEASURED FACTS THAT SHAPE THE INVARIANT (all at 8M events):
- Every fill happens at the RIGHT EDGE: right rest EMPTY, c = 0 mod 4.
- Fill-time wall law: u = topRun - 1 is in {1, 4, 5, >=6}; NEVER 0, 2,
  or 3. u odd => ABSORB (carries then f1A folds the run into the wall);
  u even >= 4 => INSULATE (two carries cap the run even and push 01
  pairs; the block is then behind single gaps forever). Depth-0 always.
- The insulate carries ARE what rebuilds the pair region: (01)^(u/2)
  over the frozen even block. The machine is: nibble pairs onto the
  wall, punch the block at the edge, halve the deposits back into pairs.
- State classes at every CE/BE (the invariant table): 39 classes.
  Dominant: C 3+runs head=1 last=even (the pair region, any wall).
  MB states always have wall-top T=1. MC singles (fills) have
  T in {2,5,6,odd>=7,even>=8}. [1,r2]-two-run states have T in
  {3,4,odd>=7,even>=8} -- NEVER T=2, which is the one death-adjacent
  class (it would punch at T'=4, u=3).

COQ (coq/Parity.v, 113 declarations, ALL Closed under the global
context): the run-level layer is PROVEN:
- runs/rside interpretation; push algebra cpush/push3 + equations.
- exc : the excursion as a TOTAL FUNCTION over any wall.
- exc_sim : (ws *> const 0) <{{F}} rside cap rs -->+ xconf (exc ws cap rs)
  by fuel induction -- excursion_gen strengthened to a computation.
- mst/mconf/mstep : the whole machine as a state-transition function;
  mstep = None exactly at the halt criterion + invariant-excluded shapes.
- be_sim / ce_gap0_sim / ce_edge_sim / ce_fill_sim (via punch_refill).
- mstep_sim : Forall (le 1) rs -> mstep s = Some s' ->
  mconf s -->+ mconf s'. STRICT progress, whole machine, one lemma.
- exc_nib : words with >=2 runs, all >=1, last EVEN pass through ANY
  excursion unchanged in those three facts (the nibble protection).

THE INVARIANT, DERIVED (to be encoded next session):
  fillok u := u <> 0 /\ u <> 2 /\ u <> 3   (u = wallTop - 1 at punches)
  Inv(MC ws rs): wallT >= 2, Forall >= 1, and by rs:
    nil       => fillok (wallT - 1)            [the c=0 edge fill]
    [c]       => even c /\ fillok (wallT - 1)  [the punch]
    c::rest   => last even /\ (head-1 two-run states need wallT >= 3)
  Inv(MB ws rs): rs <> nil, Forall >= 1, last even;
    singles [a] have a >= 4 (the absorb relaunch), giving the next
    MC-nil fill u = a + wallT >= 5 unconditionally.
  Closure sketch (verified against the abstract machine):
  - nibbles with >=3 runs: exc_nib, any wall. Exit walls are 1;1-topped
    so wallT' >= 2 always.
  - [c,r2] gap0: exc enters on a 0-topped wall => IMMEDIATE bitset exit:
    T' = 2 (c >= 2, u'=1 absorb-next) or 2+T (c=1, safe iff T >= 3).
  - fills: u odd => absorb: j=(u-1)/2 pair-pushes then ExB; j=0 gives
    MB [c+4] (a >= 4); j>=1 gives a nibble word [1^j, c+4].
    u even >= 4 => two carries reach [1, c+4] (nibble), then exc_nib.

THE ONE REMAINING QUESTION, precisely: the word grammar that excludes
[x>=2, 1, L] exactly-3-run words (their gap0 would create the forbidden
[1, L]-at-T=2 punch). The exact-3 census (--states with runs=3 split,
8M events) CONFIRMS they never occur: reachable exactly-3 words are
[1,1,L] (the last pairs, dominant), [1,2+,L] and [e,2+,L] (defect
residue, second run >= 2; one occurrence each, resolve safely: the
head-1 one at T=2 punches at T'=4 only via a 2-run [x,L] intermediate
whose gap0 gives T''=2, u=1, absorb). What is NOT yet explained: the
census right-words include 14 01 11 01 15 01 1e = [4,1,1,1,5,1,L],
whose naive head-consumption passes through [5,1,L]. It never appears
at a CE, so something in the actual event interleaving (the pushes, or
a BE skim) dissolves the 5 before it reaches third-from-last position.
NEXT SESSION OPENS HERE: add a trace mode to parity-macro.mjs that
finds a [..,5,1,L]-suffixed CE state and prints every event until the
5-run is consumed. The answer fixes the word grammar (candidate: every
non-last run >= 2 is followed by another run >= 2 until the final pair
block -- i.e. the 1*-region between the defects and L is entered only
behind a protective structure). Then: encode Inv as above, prove
closure per mstep case (the lemmas exist: exc_nib + the
bitset-immediate equation + the absorb/insulate computations on exc),
assemble with progress_nonhalt_cond (A := mst, C := mconf, P := Inv),
base case from startup, then the CI job.

MEASURE WITH: node tools/parity-macro.mjs --states 8000000 (the class
table), --fills (the u census), 20000000 (co-verification).

## THE CLOSURE, FULLY SPECIFIED (2026-08-20, session 2)

Coq green through: exc_zz / prep / exc_run_t / exc_odd_t(_nil) /
exc_absorb(_nil) / exc_insulate (the excursion computed at every call
site); w3 + w3_tail / w3_cons1 / w3_head_ge; wallT / zrun / wgap /
fillok / wallok; Inv (the full invariant, below); inv_safe (an Inv
state never hits a halt branch). All Closed under the global context.

THE INVARIANT (validated at 15,005,277 C/B-entries over 30M events in
its weak form; the strengthened form below is being validated -- run
node tools/parity-macro.mjs --inv 30000000):
  fillok u := u in {1,4,5} or u >= 7        (u = wallT - 1 at punches)
  MC ws rs: wallT >= 2, wallok, runs >= 1, and
    nil / [c]: (even c,) fillok(wallT-1), (wallT=5 -> wgap <> 1)
    [1,r2]:    last even, w3, wallT in {3,4} or >= 7
    multi:     last even, w3
  MB ws rs: wallT = 1 (singles and multi), wallok, runs >= 1, and
    [a]:    a >= 4, a even, (a = 4 -> zrun(tl ws) <> 1)
    2-run:  FORBIDDEN (never occurs)
    multi:  head = 1, last even, w3
  (The two wallT-at-MB clauses and the a=4-zrun guard are the additions
   still to re-validate; everything else passed at 30M.)

WHY EACH DANGEROUS u IS EXCLUDED: u=0 exposed-exit; u=2 carry-then-cs
re-exposes; u=3 absorb hands MB [1,c+4] whose skim punches at u=2;
u=6 the insulate cs collides with the [1,1,L] transient making
[4,1,L] (w3-dead). u=1 absorbs via j=0 (MB [c+4], relaunch); u=4
insulates to [1,c+4] then cs to [4,c+4] (g>=2 by the T=5-guard);
u=5 absorbs via j=2 (MB [1,1,4]); u>=7 generic absorb/insulate.

EXC_DEEP -- the one remaining induction (the deep excursion, entered
only from post-first-cs states), fuel induction over the wall:
  motive M ws cap rs :=
    nib rs /\ w3 rs /\ wallok ws /    (cap = false -> 2 <= rhead rs)   [the cs-merge keeps heads >= 2]
    /\ (cap = true ->
         (length rs = 2 -> 2 <= rhead rs)          [no [1,x] deep]
         /\ (length rs = 3 /\ rhead rs = 1 -> 2 <= second rs))
  conclusions:
    ExC ws' rs': nib /\ w3 /\ (length rs' = 2 -> 2 <= rhead rs')
      [so the Inv [1,r2]-T-clause is VACUOUS for deep exits]
    ExB ws' rs': nib /\ w3 /\ rhead rs' = 1 /\ 3 <= length rs'
      [deep f1A is always post-carry: prepend, never merge]
  key case facts:
  - (1,0)/cap=false is IMPOSSIBLE deep: at the cs-case the wall was
    0::0::ws', and wallok(0::0::ws') forbids ws' = 1::0::_ and 1::nil
    (the interior-singleton clauses see the leading 0). So a fresh
    cap=false state never faces (1,0); after any carry cap=true.
  - degen (0,1)/cap=true: word len>=3 or len-2-head>=2 (motive), so
    the exit never makes a [1,r2] state; wall 1;1;1-topped.
  - cs (0,0)/cap=true: push3 head-merge; w3 by w3_head_ge (old head
    >= 2 except the len-3-head-1 case, where second >= 2 makes the
    new 3-suffix (4, >=2, y) safe).
  - carries: cpush; nib_cpush, w3_cons1 / w3_head_ge.

CLOSURE CASE INVENTORY (inv_preserve : Inv s -> mstep s = Some s' ->
Inv s'), all reduced to the lemmas above + arithmetic:
 1. MB [a] -> MC ([1]^(S a)++ws) nil: T' = a+2 (wallT_MB = 1), u' = a+1
    odd >= 5: fillok. T'=5 <-> a=4: wgap' = zrun(tl ws): the a=4-guard.
 2. MB [1,...multi] -> MC rest: T' = 2+1 = 3; rest=[1,r2] needs T' in
    set: 3 ok. rest multi: w3_tail. rest=[r2]: T'=3: fillok(2)?? NO --
    MB [1,r2] 2-run is forbidden, so rest as a single arises only from
    MB [1,r2] = dead clause. rest = [c] singles come only from... (MB
    3-run [1,c2,c3] -> MC [c2,c3] 2-run, never a single). OK.
 3. MC nil (edge fill): exc(tl ws) false [3]: u = T-1 by fillok:
    u=1: exc_absorb j=0: MB [4]: Inv needs even 4 ok, a=4-guard:
      zrun(tl(1::wt)) = zrun wt: from the T=2-fill's wgap... thread:
      (T=2 -> wgap <> 2)?? -- VALIDATE, may need one more clause.
    u=4: exc_insulate + concrete g-split (g>=2 by T5-guard: cs to
      [4,4]?? entry [3]: 2 carries -> [1,4], cs -> [4,4], then
      exc_deep. g=0/blank: concrete: ExC [1;1] [4,4]-ish).
    u=5: exc_absorb j=2: MB [1,1,4]: multi, head 1, last even. OK.
    u>=7 odd: exc_absorb: MB [1^j,4]: multi OK.
    u>=8 even: exc_insulate + exc_run_t + cs + exc_deep.
 4. MC [c] (punch): same split with entry [3+c], c even.
 5. MC [c,r2] gap0: exc([0]^(S c)++ws) false [r2]: exc_zz-immediate:
    ExC (1;1;[0]^(c-1)++ws) [r2]: c>=2: T'=2, rs'=[r2] single: fillok(1)
    ok; T'=5 impossible (T'=2). c=1: T'=2+T: rs'=[r2]: fillok(1+T): T
    in {3,4,>=7} (the [1,r2]-clause!) gives u' in {4,5,>=8}: ok. And
    the T'=5-wgap-guard: T'=2+T=5 <-> T=3: wgap' = ...: thread the
    [1,r2]-T=3 states' wgap -- VALIDATE, may need one more clause.
 6. MC [c,r2,...multi] gap0: exc-immediate: ExC (...) [r2,...]: multi:
    w3_tail, last even preserved; [r2,r3] exact-2 with r2=1: T'=2 or
    2+T: the [1,r2]-T-clause at the TARGET: T'=2 FAILS the set!! --
    the source was [c,1,r3] with w3: 3-exact => 2<=c -> 1<>1
    contradiction => c=1 => T'=2+T with T>=2... c>=2 & [c,1,r3]-exact-3
    is w3-DEAD, so only c=1 survives: T' = 2+T >= 4, need in {3,4,>=7}:
    T=2 -> 4 ok; T=3 -> 5 BAD -- but [1,1,r3]-exact-3 states: measured
    T-set was {2,5,6,o,e} at runs=3 head=1 r2=1... T=3 absent. NEEDS
    the [1,1,r3]-T-clause threaded (T <> 3, T <> 5-ish). VALIDATE.
 7. MB multi -> MC: covered by 2.

VALIDATED 2026-08-20: the strengthened invariant (fillok {1,4,5,>=7},
[1,r2]-T in {3,4,>=7}, T=5-wgap-guard, wallok, MB singles even >= 4,
no MB 2-runs, MB multi head=1) HOLDS at all 15,005,277 C/B-entries
over 30M events, zero violations.

STILL TO VALIDATE-THEN-ADD before inv_preserve (one --inv round):
  - MB states: wallT = 1 EXACTLY (Coq Inv currently has >= 1; the
    closure arithmetic T' = a + 2 needs equality);
  - MB [4]-singles: zrun (tl ws) <> 1 (feeds the target's T=5-guard);
  - the T=2-fill successor guard (case 3 u=1) and the [1,1,r3]-exact-3
    T-clause (case 6 c=1) -- census both, add the minimal clauses.
Then inv_preserve is mechanical, and:

  PROVEN AND GREEN (143 declarations, all axiom-free):
    startup_anchor : c0 -->* mconf (MB [1] [4])   (exact, 8 steps)
    inv_anchor     : Inv (MB [1] [4])
    nonhalt_from_closure :
      (forall s s', Inv s -> mstep s = Some s' -> Inv s') ->
      ~ halts tm c0.
  So the whole theorem is now literally one application away:
    Theorem nonhalt := nonhalt_from_closure inv_preserve.
  inv_preserve (the seven cases above) is the ONLY open obligation.

CANDIDATE STATUS: the machine 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA
is still an OPEN BB(6) holdout. `~ halts tm c0` is NOT proven. Nothing
has been submitted anywhere, and nothing should be until it compiles.

## SESSION 3: THE CLOSURE MODEL-CHECKER, AND WHAT IT DISPROVED (2026-08-20)

Built `tools/parity-close.mjs`: literal JS mirrors of Coq's `exc`/`mstep`
(list form `excL`/`mstepL`, RLE twins for speed, cross-checked equal on
200k orbit events), a candidate boolean invariant `invbad`, an orbit
replay census, and a synthetic closure checker (CEGAR loop: enumerate
invariant states, step each with the real `mstepL`, demand the successor
satisfies the invariant; every violation prints a concrete family).

### The mod-4 fill law (the machine's real fingerprint)

At every fill, the usable top u = wallT - 1 satisfies

    u = 0 or 1  (mod 4),   u >= 1     i.e.  u in {1, 4, 5, 8, 9, 12, 13, ...}

Verified: 12,835 fills over 30M abstract events, zero exceptions. The session-2 fillok
set {1,4,5,>=7} was an OVERAPPROXIMATION: 7, 10, 11, 14, 15... never
occur, and closure genuinely fails for them. Derivation of the recursion:
odd u = absorb, j = (u-1)/2 pairs, exits MB [1^j, x+1]; the skim ladder
punches next at u' = u - 1, so j must be even, u = 1 mod 4. Even u =
insulate, cs merges the head; the surviving suffix [1^(j'), x] decays to
a punch at u' = 2j'+1, forcing u = 0 mod 4. Also confirmed at scale:
rs values are all = 0 or 1 (mod 4) (the 5s and 9s are carry-merges Q+1;
generated by the cs/carry ping-pong: +3, +1, +3, +1 from fresh 1s), rs
lasts are = 0 mod 4, MB states are exactly [1^even, Q]-shaped with
wallT = 1, MC-nil states have T = 2 mod 4, T >= 6 (born from MB [a]).

### The alternation (why the machine lives)

The orbit's fills alternate strictly: T'' = 2 mod 4 (absorb, eats one
gap 0, leaves MB) -> skim -> T'' = 1 mod 4 (insulate, cs-chain into the
pair region, exits rebuilding the wall) -> ... The gap parities, the
1-prefix parities of rs, and the wall's segment lengths are coupled so
that (1,0)-dispatches never land on a single 0 with a 1-run below
(which would make MB wallT >= 2: provably fatal two rounds later:
T' = a+1+T_MB drives u out of the mod-4 law). The T5-wgap and T6-wgap
guards of session 2 are the two smallest visible instances of this
coupling; they are NOT the whole of it.

### What the checker disproved

The session-2 plan ("inv_preserve is mechanical, seven cases") is
REFUTED. Concrete counterexample families, each a real closure failure
of the scalar invariant (state satisfies Inv, real mstep successor does
not): (1) MC-nil at T=2 (fixed by the nil birth clause); (2) interior
odd 1-runs over single-0 runs -> f1A exits with MB wallT >= 2; (3) the
degen ladder: fills at T'' = 1 mod 4 over gap 1 merge the run below,
and the resulting pure stage needs that run = 1 or 2 mod 4; (4) deeper
rungs of the same ladder, unboundedly. Attempting to close these with a
finite class quotient (values/lengths exact below a cap, mod-4 classes
above) FAILS SOUNDNESS: different caps yield different verdicts
(cap 13/29: a stage:g1 leaf; cap 61: a stage:fillok leaf), proving
per-run mod-4 classes are not a bisimulation -- the run lengths couple
ACROSS runs. The one-excursion-lookahead invariant (check every exc
exit against the invariant, recursively) is exactly "the whole future
is clean": correct but not finitely checkable with this quotient.

### The structural discovery that shapes the path forward

Over 4M events the wall's RUN COUNT never exceeds 15 (typically 7-13);
at 30M the maximum is 17. So it is not a hard constant but grows very
slowly (plausibly ~ the digit-word length |W|), while cell count and rs
length grow unboundedly. The wall
is always one huge top run over a bounded stack of small segments; the
odometer's digits live on the RIGHT side (rs: long 1-blocks between
values). So the reachable set is: bounded wall shape vector (<= 15
runs, lengths parameterized with mod-4 side conditions) x structured
rs language. The second wall segment's length drifts upward through
all mod-4 classes over time, so segment lengths cannot be finitely
classified independently -- the coupling is relational.

### Honest status and viable architectures

PROVEN AND GREEN (unchanged, 143 declarations, axiom-free):
`nonhalt_from_closure : (forall s s', Inv s -> mstep s = Some s' ->
Inv s') -> ~ halts tm c0`, `startup_anchor`, `inv_anchor`, `mstep_sim`,
`exc_sim`, all call-site equations, `exc_deep`. The reduction of
nonhalt to closure-of-an-invariant stands. What session 3 established:
the Inv that closes is NOT the session-2 scalar Inv; any candidate must
pass `parity-close.mjs --close` (synthetic) AND `--replay` (orbit)
before Coq encoding is attempted. Architectures, in order of promise:

A. Parameterized family progress: exploit the bounded run count. Find
   the explicit closed form of the reachable states (wall shape vector
   + rs grammar indexed by the odometer count), prove the round
   transformation once, apply progress_nonhalt_cond with the family as
   index. This is the Odometer-M4 architecture; the bounded wall makes
   the family finite-dimensional. Needs: the round-boundary closed
   form (empirical next step: census states at round boundaries).
B. Rebuild the invariant with relational clauses (differences/sums of
   run lengths mod 4, the alternation phase as explicit state). The
   checker is the instrument; expect multiple CEGAR rounds and a much
   bigger Coq encoding (the exc_deep-style induction must carry the
   full motive).
C. Both fail -> the machine's true invariant may be inherently
   history-like; would need a genuinely new idea.

`~ halts tm c0` is NOT proven. The parity machine remains an open
BB(6) holdout. Nothing has been posted anywhere.

### The base-state family (the closed form, empirically)

States with wall <= 2 runs and top <= 1^2 (`--rounds` census; rs in RLE):

    ev 2       B [1^1]  1x2 4                      ev 1009   B [1^1]  1x2 9 1x30 72
    ev 5       C [1^2]  4 8                        ev 1239   C [1^2]  4 1 9 1x22 104
    ev 22      B [1^1]  1x6 12                     ev 1507   C [1^2]  8 1 9 1x6 168
    ev 29      C [1^2]  4 1x4 16                   ev 2525   B [1^1]  1 9 1x92 44
    ev 40      C [1^2]  8 1x2 24                   ev 3250   C [1^2]  4 9 1x84 76
    ev 125     B [1^1]  1x18 20                    ev 4508   C [1^2]  8 9 1x68 140
    ev 144     C [1^2]  4 1x16 24                  ev 6256   C [1^2]  12 9 1x36 268
    ev 179     C [1^2]  8 1x14 32                  ev 22439  B [1^1]  1x3 9 1 5 1x112 384
    ev 237     C [1^2]  12 1x10 48                 ev 25610  C [1^2]  4 1x2 9 1 5 1x80 512
    ev 305     C [1^2]  16 1x2 80                  ev 28880  C [1^2]  8 1x2 9 1 5 1x16 768
                                                   ev 96624  B [1^1]  1 9 1x2 9 5 1x200 872
                                                   ev 341373 B [1^1]  1x4 5 1 5 9 1x504 1336

Shape: rs = [HEAD (4,8,12,... inner-loop ladder with shrinking 1-block),
W (a slowly-evolving word over {5, 9} with short 1-blocks -- the
odometer's high digits), 1^K (K large, shrinking within an epoch),
L (large, growing ~ +4 x consumed)]. Within an inner round the head
climbs by 4 and K drops; per epoch W increments like a counter and a
new digit appears every ~4x events. This is the parameterized family
for architecture A: F(W, inner-state, K, L) with the two lemmas
(inner-round transformation; epoch/digit-increment) to prove in Coq.

### The round recurrence and the conservation law (`--recur` census)

At canonical base states C [1^2] [H, W, 1^K, L], every within-round step
(dH = +4) satisfies EXACTLY:

    K -> K - D,   L -> L + 4D,   D -> 2D      (D a power of 2)

so **L + 4K is conserved within an epoch** (measured: 88,88,88 /
412,412 / 6712,6712,6712 / ...), and D doubles per round: the binary
doubling engine. Epoch boundaries (H resets to 4, W increments like a
counter over {5,9}-digits) re-initialize (K, L, D) from the mass, which
roughly doubles per epoch. Architecture A is therefore fully specified:

    round lemma:  base(W, H, K, L, D) -->+ base(W, H+4, K-D, L+4D, 2D)
                  (induction over the D-drain; reuses the excursion
                   machinery: decay-pump, fill, absorb/skim, cs-descent)
    epoch lemma:  K < D case: -->+ base(incr W, 4, K', L', D')
    nonhalt:      progress_nonhalt_cond over the family; no closure
                  invariant needed -- the family IS the invariant.

Open detail for the round lemma: the family's MID-round states carry
the wall's transient segments (<= 15 runs, measured); the phase lemmas
must thread them explicitly.

### Why architecture A needs NO new tape-level work

mstep and exc are FUNCTIONS. The round and epoch lemmas are therefore
mstep-iteration computations at the mst level: `mstep^n (base params) =
Some (base params')`, provable by induction over the drain counters
with the EXISTING call-site equation library (exc_run_t, exc_absorb,
exc_insulate, exc_zz, plus small new equations if the phase shapes
demand them) discharging each parameterized exc computation. mstep_sim
(proven, strict progress) lifts every mstep step to `-->+` on the tape,
and progress_nonhalt_cond closes nonhalt over P s := exists params,
s = base params. The startup already lands in the family (the anchor
MB [1] [4] = the ev-2 base row). Remaining work is therefore: (1) the
mid-round phase-state shapes (symbolically run one round through the
equations; wall stays <= 15 runs), (2) the round lemma's drain
induction, (3) the epoch lemma's digit-word carry, (4) assembly. All
arithmetic + function computation; no new excursion inductions.

### The lap grammar: the wall tail IS a binary counter (`--roundtrace`)

One round (dH = +4) = 2^r laps, each lap = pump + fill. Laps alternate:
A-lap (absorb, T even at fill): eats ONE 0 of the leading gap, restores
the rs prefix, L += 4. I-lap (insulate, T odd): a cs-cascade that
INCREMENTS the wall tail read as a binary counter: blocks `0^2 1^2` are
digits; the cascade consumes carry-digits (cs eats 0^2, the carry-merge
eats 1^2, head += 4 per layer) until it can exit; the rs prefix drops 2
per... (per-lap: 0 or 2, doubling per round via the carry structure).
Round 5 trace (evs 179-237): tails `0^7 1^2` -> `0^6 1^2` ->
`0^3 1^2 0^2 1^2` -> `0^2 1^2 0^2 1^2` -> collapse. Round 6: the same
with one more digit. The leading `0^a` counts down (a: absorb -1,
insulate -4 or carry). So: rounds = the tail-counter counting 2^r laps,
epochs = the rs digit-word W counting rounds, the whole orbit = nested
odometers. The ONE new Coq lemma-family needed: the carry cascade

  exc ((0^2 ++ 1^2)^k ++ rest) with cap: k cs+merge layers, head += 4k,
  continue at rest

by induction on k from the existing dispatch equations; then lap
lemmas, the round induction over the tail counter, the epoch carry.

### Session 3 close: the lap layer is GREEN (163 declarations, axiom-free)

New in coq/Parity.v (all Closed under the global context):
blocks/iter4/exc_blocks (the binary-counter cascade equation),
mrun/mrun_app (iterated macro steps), mstep_pump/mrun_pump/wpump,
mstep_skim, mstep_bury, mstep_absorb, mstep_insulate_exit,
mstep_insulate_carry, and the composed laps:

  lapA      : mrun (S n + 2) from (top 2, prefix S n, gap 0::wt, word L)
              to (top 3, prefix n, word L+4)          [pump, fill, skim]
  lapI_exit : mrun (S n + 1) from (top 3, prefix S n, gap 0^(4+g))
              to (top 2, gap 0^g, head 4 ready to bury)
  lapI_carry: mrun (S n + 1) from (top 3, prefix S n, gap = k+1 blocks
              over blank) to the rebuilt base [1^2] with head via iter4

Remaining for Theorem nonhalt (three designed blocks, in order):
1. The round induction: compose bury + lapA + bury + lapI over the
   tail counter (induction on the counter value in blocks form),
   producing round(W,H,K,L,D) -> round(W,H+4,K-D,L+4D,2D).
2. The epoch carry: the K < D case increments the rs digit word W
   (the {5,9} digits) -- same cascade pattern one level up.
3. Assembly: family F, mrun -> -->+ bridge (mstep_sim chained; needs
   mstep preserves rs-positivity, an easy exc induction), then
   progress_nonhalt_cond over F. Startup already lands in F.

## SESSION 3 FINAL: blocks delivered and the exact remaining obligation

DELIVERED GREEN (178 declarations, all Closed under the global context,
through this commit):

Block 3 COMPLETE -- the assembly:
  exc_pos / mstep_pos (positivity through excursions and macro steps),
  mrun_progress (mrun chains lift to -->+ via mstep_sim/progress_trans),
  Theorem nonhalt_from_family :
    forall F, F anchor -> (F -> positive rs) ->
    (forall s, F s -> exists n s', mrun (S n) s = Some s' /\ F s') ->
    ~ halts tm c0.

Block 1 PARTIAL -- the chunk generators (the W-nil fragment):
  chunkBig / chunkCascade / chunkTerm over the stack family
  MC (1;1;stackw gs) (H :: prep p [L]), plus the full lap toolkit
  (lapA, lapI_exit, lapI_cascade, lapI_carry, mstep_* equations,
  blocks/iter4/exc_blocks).

REMAINING (the one obligation: exhibit F and its closure), variant
inventory read off the traces:
  V4 accumulator-cascade: stack entries are (gap, run) with runs >= 2;
     cascades ending at a run r: r odd -> f1A exit carrying rs digits
     (the 1^r run is a unary accumulator; digits {5,9} are born here),
     r even -> merged exit top. Generalize stackw to (gap, run) pairs
     and add the two exit lemmas.
  V5 digit-bury chunks: heads 5/9 bury 0^4/0^8 (mstep_bury covers the
     shape; the chunk composition mirrors chunkBig).
  V6 the p-exhaustion chain (epoch boundary): prefix 0/1 entries:
     the T=2 punch (mstep_absorb j=0), MC-nil absorb (needs
     mstep_absorb_nil, trivial mirror), the g=1 degen insulate (needs
     mstep_insulate_degen: exc_insulate + run_t + (0,1)-degen, exits
     top-4), top-4 pump re-entries.
  V7 epoch terminal: the mass rebirth into the next base (composition
     of V6 pieces; the digit word increments).
  Then: Inductive F covering base/chunk-boundary/epoch-phase shapes
  with side conditions, the closure case analysis (each case = one
  chunk/variant lemma application), and
    Theorem nonhalt : ~ halts tm c0 := nonhalt_from_family F ...
  Validate every variant statement against parity-close.mjs traces
  BEFORE encoding (the standing rule).

### Family inventory, first data (`--family` mode, session 3 end)

Boundary candidate: MC, wall top run = 2, rs head >= 4. Findings at 2M
events: (a) the proven chunk n-formulas verify in vivo (chunkBig at
p=12: n = 31 = 1 + (S(S p)+2) + (S p+1) exactly); (b) hop behavior is
determined by the rs head class {4, 5, 9, other Q} x (prefix zero?) x
the TOP TWO stack entries only -- the deeper stack is passive context,
matching the chunk lemmas' `rest` parameter; (c) the boundary set must
also include the top-4 states (degen exits inside epochs land there;
with top-2-only boundaries the hops span two chunks); (d) mid-epoch
stack entries are (gap, run) pairs with gap in {2,3,6,7,8,11,...} and
run in {2,3,4,...,X}, the run being the unary accumulator. Next
session: add top-4 boundaries, re-inventory (expect ~20-30 closed
types), define FState + per-type chunkstep in JS mirroring the intended
Coq lemma statements, validate the full orbit as a chunkstep chain,
then transcribe: Inductive F, closure cases, and
Theorem nonhalt := nonhalt_from_family F.
