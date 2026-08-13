# The Odometer: analysis of BB(6) holdout `1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA`

Status: work in progress. Verified = proven by our symbolic chain prover
(exact BigInt affine arithmetic over formal parameters, every step mirroring
the concrete simulator, cross-checked against concrete execution at every
anchor with zero mismatches). NOT yet independently verified in a proof
assistant; Lean translation is the end goal. Conjectures are labeled as such.

## 0. Conventions

- Machine in standard text format above; states A–F; `---` (state D, symbol 0)
  is the unique halt transition. Start: state A, all-zero tape.
- We simulate at block size k=4: the tape is partitioned into 4-cell blocks,
  written as 4-bit words (leftmost cell = least significant bit in our run
  dumps, rendered as bit strings, e.g. `1110`).
- Configurations are run-length encoded: `B^n` = n consecutive copies of
  block B. `[C>]` = head at the right edge of the written tape, in state C,
  facing the infinite blank region.
- An **anchor** is any moment when the machine is in state C at the right
  edge facing right. Empirically the machine returns to anchors throughout
  its life. **N** denotes the count of the `1110`-run adjacent to the right
  edge (below); N increments by exactly 1 per anchor visit.

## 1. Verified results (chain prover, session of 2026-08-13)

### 1.1 Epoch-3 theorem
For all M ≥ 2, N ≥ 1:

```
0^∞ 1101 0101^4 0111 1101 0101 0111^M 0101^5 1111 0111^N 0101 [C>] 0^∞
  →(exactly 8M + 1024N + 36936 steps)
0^∞ 1101 0101^4 0111 1101 0111 1101^(M−1) 1111 0101^5 1111 0111^(N+64) 0101 [C>] 0^∞
```

(k=1-cell rendering of blocks; from tools/chain.mjs run `30 64 202`.)

### 1.2 Generation theorems j=16..20
Let "collapse anchor of generation j" be the anchor at N = 2^j − 2 whose
digit zone is a single run (`1010^K`). Verified by a continuous symbolic
chain of 1,048,575+ anchor transitions (0 mismatches vs concrete through
t=483,899; parameters M, N formal throughout, final side condition M ≥ 4):

| j  | N = 2^j−2 | K  | M offset | steps coeff of N (÷2^18) | steps coeff of M | constant term    |
|----|-----------|----|----------|--------------------------|------------------|------------------|
| 16 | 65534     | 13 | M        | 1                        | 8                | 2148554104       |
| 17 | 131070    | 14 | M−1      | 5                        | 8                | 53692443344      |
| 18 | 262142    | 14 | M−1      | 13                       | 16               | 362938652012     |
| 19 | 524286    | 15 | M−2      | 29                       | 16               | 1806064790212    |
| 20 | 1048574   | 16 | M−3      | 61                       | 24               | 7990851949928    |
| 21 | 2097150   | 17 | M−4      | 125                      | 24               | 33554565802688   |
| 22 | 4194302   | 17 | M−4      | 253                      | 32               | 137458551641412  |
| 23 | 8388606   | 18 | M−5      | 509                      | 32               | 556372755851932  |
| 24 | 16777214  | 19 | M−6      | 1021                     | 40               | 2238626094404908 |

(steps measured from the N=49150 anchor with M=194 formal; final side
condition M ≥ 7 for the full 16.7M-transition chain; templates in
tools/factory.mjs output, committed. j=21..24 N-coefficients were PREDICTED
by C1 from the j=16..20 fit before the verification run produced them: 4/4.)

The composed chain through j=24 is itself a theorem: for all M ≥ 7, N ≥ 1,
from the epoch-13 start config the machine runs exactly
40M + 267649024N + 2238626094404908 steps (≈2.25×10^15 at the machine's true
values M=194, N=49150) to the generation-24 collapse with M−6, N+16678914.

### 1.3 Composed mega-theorem
For all M ≥ 4, N ≥ 1: from the epoch-13 start config (N-run = N, M-run = M),
the machine reaches the generation-20 collapse config (M-run = M−3, N-run =
N+999424) in exactly 24M + 15990784N + 7990851949928 steps.

## 2. Verified-empirical invariants (exact over observed range, no ∀-proof yet)

- **Budget invariant**: M + K = 207 at every collapse anchor observed
  (j=16..24 symbolically; every anchor of the machine's first 8.9×10^13
  steps concretely, via the epoch logger).
- N increments by exactly 1 per anchor visit (concrete, full observed range).
- **Payment/borrow law** (observed j=16..24): M pays −1 at thresholds
  N+2 = 2^a and N+2 = 3·2^a; M borrows +1 at thresholds N+2 = 5·2^a (once
  per 4 generations); K stalls exactly at borrow generations (K cadence
  +1,+1,+1,0 repeating). Net: M drains 3 per 4 generations.
- The preamble (runs left of the M-run) cycles through variants, each held
  for ~2 generations: tail sequence observed
  [1010^3], [1010^2 1110 1011], [1110 1011 1010 1110], [1110 1011 1110 1011],
  [1011 1010^2 1110] — a slow register with its own carry structure (C4).

## 3. Conjectures

- **C1 (coefficient recursion)**: the steps N-coefficient of generation j is
  c_j = 2^18·(2^(j−14) − 3) — equivalently c'=2c+3·2^18. Verified j=16..24;
  the j=21..24 values were predicted from the j=16..20 fit before the
  verification run (4/4 correct). Still a conjecture for j > 24 pending the
  general induction.
- **C2 (collapse cadence)**: collapse anchors occur at every N = 2^j − 2,
  j ≥ 16 (and an analogous pre-2^16 cadence with odd multipliers).
- **C3 (budget)**: M + K = 207 at every collapse anchor, for the machine's
  entire life.
- **C4 (preamble register)**: the runs left of the M-run form a bounded
  numeral ("preamble register") ticking once per generation; it determines
  when M pays vs borrows, and generates the {5,3,1,3,3,1,...} odd-part
  pattern of the pre-2^16 era.
- **C5 (endgame)**: with the payment/borrow law (−3 per 4 generations from
  M-offset 0 at j=16, M=194), M-bottom (K→207) lands near generation
  j ≈ 16 + 194·(4/3) ≈ 275, i.e. N ≈ 2^275 and total steps ~ 4^275/2^10
  ≈ 10^160. The halt transition (D,0) may become reachable there; the
  machine's fate is decided at that scale, forever beyond simulation.

## 3.1 Registered predictions (written before the verifying runs)

- **P-2026-08-13-a** (third payment/borrow period, generations 25–28; run
  not yet performed at time of writing): borrow +1 at N+2 = 5·2^22 =
  20971520; payments −1 at N+2 = 3·2^23 = 25165824, 2^25 = 33554432,
  3·2^25 = 100663296, 3·2^26 = 201326592. Collapse K values: j=25→20,
  j=26→21, j=27→21, j=28→22; M offsets at collapses: −7, −8, −8, −9.
  N-coefficients (÷2^18): j=25→2045, j=26→4093, j=27→8189, j=28→16381.
  (Note 3·2^25 > 2^26−2, i.e. the 3·2^25 payment lands inside generation
  27; ordering of events within periods follows the period-2 pattern.)

  **GRADED (run completed same day, 31.3 min, chain to N=2^28, final side
  condition M ≥ 10, total verified span ≈5.8×10^17 steps):**
  - Schedule events: **5/5 exact** (all five thresholds hit, no extra
    events). Third full period confirms the 5-event period-4 schedule.
  - N-coefficients: **4/4 exact** (2045, 4093, 8189, 16381).
  - K values: 3/4 — actual (20, 20, 21, 22): the stall pair is (25,26),
    not (26,27). Corrected law, fitting ALL data j=17..28: **K (and the
    M-offset) stall in the generation-pair containing the borrow** (borrows
    land in generations 4m+1: 17? no — 21, 25 observed; stalls (21,22),
    (25,26); earlier stall (17,18) ↔ borrow at 5·2^14 in generation 17 ✓).
  - M offsets: 3/4, same single phase error, same correction (−7,−7,−8,−9).
  - M+K = 207 at all four new collapses (through N = 2^28). Invariant now
    exact over the machine's entire life to ~5.8×10^17 steps.
  - **Preamble verdict: drifting counter, NOT a short cycle.** Tail
    spellings tick once per generation-pair, all seven observed states
    distinct (j=16..28), and at j=28 the carry reached the frozen head for
    the first time (`1011 1010^3 1111` → `1011 1010^3 1111^2`) — the first
    observed super-period event. The schedule stayed exact through it;
    whether period 5+ (j ≥ 33) shifts is the open question for the j=32 run.

- **P-2026-08-13-c** (rulebook family structure; registered before running
  the family analysis): the 1,541 sealed lemmas collapse under "skeleton
  grouping" (same pre block-sequence, counts allowed to vary) into **at most
  ~120 families**; the largest families are the `1111^k` carry ladders
  (k = digit-sum accumulation); **most families vary in exactly one count
  position**; and every varying count position varies over a contiguous
  integer range (no gaps), consistent with each family being one symbolic
  lemma instantiated along the K-growth of successive generations.

  **GRADED (tools/families.mjs, same day):** 35 families (✓ vs ≤120; 9
  singletons = birth + event lemmas). "Most vary in exactly one position"
  ✗ — the mode is 3–5 varying positions (the numeral low-window spells
  several digits at once). "Contiguous ranges" ✗-partial — ~half the ranges
  are arithmetic progressions of step 3 (e.g. `1111`-counts 1,4,7,10) or
  bimodal {1, big}: the mod-3 classes are the M+K budget's +3/period cadence
  showing up in the census, structure rather than noise.

- **P-2026-08-13-d** (∀-form lift; registered before running tools/lift.mjs):
  proving each family ONCE with every varying count position replaced by a
  free formal parameter (family-constant counts kept concrete) will succeed
  for **≥ 25 of the 35 families**, failures concentrated where a varying
  count participates in a carry cascade (value/parity-dependent branching);
  a residue split (n → 2m+r or 3m+r, still affine) rescues the failures.
  The lifted rulebook re-applied to all 266,388 observed transitions will
  keep coverage at 100.000% (minus the N=2 base case) with 0 mismatches.

  **GRADED (tools/lift.mjs v3, same day):** coverage retention ✓ (100.000%,
  0 mismatches), rescue-by-specialization ✓ in mechanism but value-PINNING
  (recursive refinement: pin each below-bound or failure-implicated observed
  value, keep the rest formal) is what worked, not residue splits — residue
  structure never needed to enter the lemma language. Three iterations to
  get there: naive lift covered 12.5% (side conditions exclude the p=2
  workhorses), success-only refinement 50.0% (forests died at failed
  intermediate nodes), failure-recursion refinement **99.006% via lifted
  ∀-lemmas**. Final book: 648 lifted ∀-lemmas + 428 concrete small-count
  pins (from 1,541 concrete lemmas), still 100.000%/0-mismatch over the
  266,388-transition census.

- **P-2026-08-13-e** (per-lemma invariant audit; registered before running
  tools/audit.mjs): over the 1,076-lemma working book, (1) every lemma
  grows the N-run count by exactly +1; (2) every lemma conserves the
  block-extent of the window LEFT of the tail separator (digit rewrites
  are in-place; RLE counts shuffle but the total block count of the
  pre-window equals the post-window, after accounting +1 to the N-run and
  the context marker), with the ONLY exceptions being the finitely many
  event lemmas (borrow/pay/collapse/leader), where the extent shifts by
  exactly the amount absorbed or released by the reservoir run inside the
  window. M+K=207 is the global shadow of this local law.

  **GRADED (tools/audit.mjs, same day): better than predicted.** N-run +1:
  2,371/2,371 non-birth lemmas hold, 0 violations. Extent conservation:
  2,371/2,371, 0 deviations — the predicted event-lemma exceptions DO NOT
  EXIST: borrow/pay exchanges live inside the lemma window (reservoir run
  included), so extent is conserved there too. Corollary chain: every
  covered sweep preserves total block extent left of the separator
  (= 215: preamble 8 + reservoir M + zone K + merged digits) and
  increments N by 1. C3 (M+K=207) and the N-cadence are now per-lemma
  THEOREMS over the book — the only remaining gap to ∀-time is closure
  (every future transition matches the finite book), which is the counter
  induction's job.

- **P-2026-08-13-f** (residue structure + closure; residue part measured
  same day, closure registered before building tools/closure.mjs):
  MEASURED — every multi-use lemma is residue-pure with depth 3–17 (all
  uses agree mod 2^depth; ρ₂ of gcd of use-differences); 219/292 are
  dense (fire at every ν of their class over their active range), the 73
  sparse ones split classes with siblings via deeper spelling context.
  PREDICTION for the closure checker: starting from the ~63 windowed
  post-carry shapes with big counts formal, symbolic application of the
  book maps every shape into the same shape set (with affine count
  updates), with deep-carry emissions absorbed consistently — i.e. the
  window automaton CLOSES, and the only open interface is the finite
  deep-carry emission protocol (single-digit handoffs at the context
  boundary).

- **P-2026-08-13-b** (fourth period, generations 29–32; registered before
  the j=32 run): borrow +1 at N+2 = 5·2^26 = 335544320; payments −1 at
  3·2^27 = 402653184, 2^29 = 536870912, 3·2^29 = 1610612736,
  3·2^30 = 3221225472; no other M-events. Collapse K values: j=29→23,
  j=30→23 (stall pair (29,30): borrow lands in generation 29), j=31→24,
  j=32→25. M offsets: −10, −10, −11, −12. N-coefficients (÷2^18): 32765,
  65533, 131069, 262141. M+K=207 throughout. Null hypothesis on the j=28
  head-carry: no schedule change within this period.

## 4. Proof roadmap

1. Preamble register law (finite-state; enumerate variants across
   generations j=16..24+). → replaces C4 with a lemma.
2. General generation theorem G(j) by induction: express all shapes affine
   in (M, N, P:=2^j); the induction step needs "regex families" (repeated
   digit segments with symbolic arity) — the numeral has ~j digits mid-epoch.
   Binary-counter sub-induction is standard; the budget layer is the novelty.
3. Endgame: instantiate G at M-bottom, run the final regime concretely from
   the constructed config (RLE counts are BigInt — astronomical N is fine).
4. Lean formalization of 1–3; submit to bbchallenge.

## 4.1 Build B architecture (settled by first context-abstracted runs)

No starred-segment language needed: RLE already collapses uniform digit
stretches, and single sweeps only touch the tape's right end. The engine is:

- **Context abstraction** (`src/family.mjs`): a lemma proven from a config
  whose left stack bottoms out in a CONTEXT marker is valid for every tape
  content beyond it — sound because the symbolic run aborts if the head
  ever consumes the marker (tape locality). Implemented; first runs show
  the sweep dynamics never touch context through ≥8 sweeps.
- **Phase automaton**: the numeral's low digits cycle through a finite set
  of local tail shapes, one transition per sweep, while the high-digit run
  drains (observed: `1010^(n1−k)` dropping ~1 per 2 sweeps, low pattern
  churning through 1111/1011/1110-flavored spellings). Each transition is a
  provable 1-sweep ∀-lemma with affine map + side conditions.
- **Harvester** (to build; v1 falsified a shortcut): exact-state cycle
  detection fails — a 400-sweep context-abstracted walk (tools/harvest.mjs)
  produced 401 distinct exact states with zero context touches, because the
  low window wraps only at numeral scale. v2: dedupe individual EDGES
  (pre-template → post-template 1-sweep lemmas, params re-normalized per
  shape), build the automaton graph offline, compose paths algebraically.
  Carry events needing deeper tape appear as context-touched → widen the
  window and reprove (adaptive window widening).
- **Composition**: epoch theorem = path composition through the automaton;
  the doubling induction (T(2Q) from two T(Q)) rides the automaton's cycle
  structure with Q affine.
- **Census (266,389 anchors, 4M macro-ops)**: the active tail vocabulary is
  12 distinct 4-run templates (24 at width 5; count classes 1/2/big). The
  8-run figure of 1,583 is passive-context inflation. So the machine-level
  half of the formal proof is an enumeration of a few dozen
  context-abstracted sweep lemmas (d-symbolic carries included); the
  remainder of the proof is numeral arithmetic with no TM content — the
  Lean-friendly half. Proof structure: (1) finite TM-lemma set, machine-
  verified; (2) counting-system induction on top, TM-free.

## 4.2 The rulebook (milestone 1 of the formal proof)

`tools/lemmas.mjs` enumerates every observed anchor-tail template (counts
≤100 concrete, >100 symbolic; adaptive window 5→8→12→full-config) and
proves a one-sweep lemma for each. **SEALED** over 266,389 anchors (first
13+ generations):

- **1,541 proven ∀-lemmas, 100.000% coverage (266,387/266,388), 0
  mismatches.** The single uncovered transition is at N=2 — the machine's
  third sweep, part of the concrete base case by definition. Full rulebook
  in `data/rulebook.txt`.
- Key design decisions that got here: (a) context abstraction (lemmas valid
  for all tape content beyond the window, by locality); (b) symbolic loop
  collapse in `symbolicRun` (shape recurrence with constant count drift,
  single −1 drain → jump t*=drained−1 cycles as one affine step); (c) the
  **symbolization threshold at 100**: only the genuinely unbounded
  registers (M, N) become formal variables — every K-scale count is bounded
  by the M+K=207 conservation law and stays concrete, so event-sweep drains
  (−3/cycle on the leader) unroll concretely instead of demanding modular
  case splits. K-generality belongs to the arithmetic layer, not the tape
  mechanics.
- Regressions at seal time: validate ALL PASS, hunt self-test 40/40 with 0
  cross-fails, epoch-3 theorem byte-identical.

Proof status ladder: milestone 1 (rulebook) ≈ done pending event lemmas;
milestone 2 = numeral-arithmetic layer (TM-free); milestone 3 = endgame at
M-bottom; milestone 4 = proof-assistant port (community standard is
Coq/busycoq rather than Lean; target that).

## 4.3 Milestone 2 architecture (settled 2026-08-13, session 5)

**M2a — family census** (`tools/families.mjs`, done): the 1,541 sealed
lemmas collapse into 35 skeleton families (9 singletons = birth + event
lemmas). Varying count positions form mod-3 progressions (the budget
cadence) and {1, big} bimodals.

**M2b — the ∀-form lift** (`tools/lift.mjs`): one symbolic lemma per
skeleton with every varying-or-big count position formal; the engine's
side conditions (runs can't be consumed to zero while formal) exclude small
values, so each excluded observed value gets a specialized re-proof with
that value pinned (recursive refinement → a finite lemma FOREST per
skeleton). Union = finite, j-independent rulebook: formal params cover all
values ≥ n0, pinned lemmas cover the finitely many below. Soundness of
application at any width: a proven context-abstracted lemma never popped
beyond its window's top run (doing so would have aborted context-touched),
so splitting a larger host run into (context excess + window top) is a
tape no-op — lemmas apply inside any host config whose tail matches.

**M2c/M2d — composition calculus** (`src/compose.mjs`, to build): the
TM-free layer. A lemma is an affine map on tail shapes with side
conditions; composition of lemma words is shape unification + affine
substitution + side-condition pullback (all exact BigInt, no tape
simulation). Generation structure: infer the lemma-word grammar of one
generation empirically from the chain logs (`tools/grammar.mjs`), expect
counting-segment words W_d (2^d sweeps) with the doubling recurrence
W_{d+1} = W_d · X_d · W_d. Key algebraic fact making ∀j expressible in the
EXISTING engine: the generation maps' linear parts are integer-constant;
only offset vectors carry 2^d terms, so introducing P := 2^d as one more
formal parameter keeps everything affine (doubling = the substitution
P := 2P, also affine). The c' = 2c + 3·2^18 coefficient recursion is the
predicted fingerprint of W_{d+1} = W_d X_d W_d at the steps coordinate.
Endgame composition is then LINEAR in j (compose ~constant many macro-maps
per generation, generations 16..~275), not exponential.

## 4.4 The number system, decoded (session 5)

Digit symbols (zone runs, one digit per repeated block): O=`1010`=0,
e=`1110`=1, a=`1011`=2, f=`1111`=3. Writing ν = N+2 = 2^(L+1) + v with L
zone digits (p_{L−1}…p_0 left to right), verified mechanically over all
132,892 post-birth anchors:

- **Sliding-window law (EXACT, all anchors, no exceptions):** p2 = ⌊v/2⌋
  mod 4 and p3 = ⌊v/4⌋ mod 4 — the two low positions hold OVERLAPPING
  2-bit windows of v (they share a bit). This redundancy is the increment
  engine: the shared bit is what lets one sweep advance the counter with
  O(1) local work. p1/p0 are head-phase cells (v mod 2 driven).
- **Plain-bit law (exact for v < 64):** p_i = bit_i(v) for i ≥ 4, spelled
  f at even positions and e at odd positions (the 4-cell block phase).
- **Merge law (discovered via the v ≥ 64 failure wall):** a deep zone
  digit spelled with the same block as the adjacent M-reservoir run MERGES
  into it (RLE). The reservoir count therefore carries merged digit debt —
  this IS the M-offset drift we have tracked since session 1, and why
  M + K = 207 is exact: tokens flow between spelled digits and the merged
  run without loss. Failure intervals [(2^k+1)·2^6, 2^(k+3)) in every
  generation = precisely the anchors where p6+ is set.
- **Debt spellings:** during borrow windows (first fails at ν = 5·2^4,
  5·2^5, 5·2^6 before the merge wall) the event position holds a (=2) — a
  double token parked in the zone until the payment sweeps repay it. The
  payment/borrow schedule is digit arithmetic in the open.

Proof consequence: the abstraction map α(config) = ν is now explicit
(windowed digits + merge-aware reservoir accounting). Milestone-2 plan:
α-preservation per lemma (finite symbolic check over the 1,076-lemma book:
each lemma's post decodes to pre's value +1) + counter arithmetic for the
generation theorem — no tape content anywhere.

**α value-congruence status (tools/alpha.mjs Part 1):** with digit values
O=0, e=f=1, a=2, the congruence v̂ ≡ ν (mod 2^visible) is exact for all
anchors whose visible zone stops below the first a-digit, and fails by
exactly a factor-2 overcount at deep a's outside debt windows (first
cases: ν = 9·2^6-era anchors with a at p6). OPEN: the a-digit is DUAL —
value 2 (parked borrow debt, e.g. at pay thresholds 3·2^k) vs value 1
(plain deep set bit spelled `1011` — hypothesis: deep 1-spelling tracks
the reservoir's alternating block 1110/1011 so the merge seam stays
block-compatible; the reservoir phase is then part of the decode key).
Next session: split deep-a by reservoir phase, re-validate, then Part 2
(per-lemma +1 at parameter samples, carry-out bucketing).

## 4.5 Segment-map findings (why the induction lives on the numeral)

Composed segment-interior maps (tools/segmap.mjs) are guarded-affine and
compose EXACTLY (0 irregular over all depths), but their guard values pin
carry-history debris — records fragment at every depth (no finite
inventory at fixed depth). Windowed post-carry boundary shapes DO form a
depth-stable ~63-shape inventory (tools/grammar.mjs), but the A-drift of
the data is popcount-flavored, not affine. Conclusion: the ∀j induction
must run on the decoded numeral (α above), not on segment maps.

## 5. Reproduction

- `node tools/validate.mjs` — simulator exactness (BB(2)–BB(5) step counts).
- `node tools/chain.mjs 30 64 202` — epoch-3 theorem.
- `node tools/factory.mjs 49150 1100000 194 8000000` — generations 16–20.
- `node tools/epoch.mjs 50000000` — concrete epoch table from birth.
