# The Odometer: analysis of BB(6) holdout `1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA`

Status: work in progress. Verified = proven by our symbolic chain prover
(exact BigInt affine arithmetic over formal parameters, every step mirroring
the concrete simulator, cross-checked against concrete execution at every
anchor with zero mismatches). NOT yet independently verified in a proof
assistant; Coq/busycoq port is the end goal (community standard).
Conjectures are labeled as such. A fresh session should read this file
top to bottom, then §4.3–4.5 for current state; every claim is
re-derivable via §5.

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
  pattern of the pre-2^16 era. **DECODED 2026-08-14 (P-2026-08-14-d in
  §3.1): the preamble spells s = ⌊log₄ ν⌋ in an 8-cell SPELL-style
  numeral, exact on all 15 observed states; graded predictions pending
  the j=32 chain.**
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

- **P-2026-08-14-a** (bit-cell font overlay; registered before running
  tools/font.mjs): the only remaining spelling freedom is which glyph a
  settled bit cell (index 3m+4) uses for its value. Predictions:
  (1) **1-fonts by tier parity** — the v<64 observation "f at even
  positions, e at odd" generalizes: each bit cell's 1-glyph is fixed for
  life at birth, alternating f/e by tier (cell 4 = f, cell 7 = e,
  cell 10 = f, cell 13 = e — or the complement; the fit decides which).
  (2) **0-fonts are O except during open borrow windows**
  [5·2^k, 3·2^(k+1)), where exactly one implicated cell spells a (the
  parked double token), plus merge-adjacent deep cells spelled in the
  reservoir's current font. (3) **Era-constancy** — within one calendar
  era every (cell, value) pair uses ONE glyph; font changes happen only
  at the 22 calendar events. Falsifier: any cell whose 0/1 glyph varies
  within an era on non-merged anchors.
  **GRADED (tools/font.mjs): (1) ✗, (2) ✗, (3) ✓-subsumed — the truth is
  simpler than every guess: bit cells spell 0 = O and 1 = f, at every
  tier, in every era, with ZERO mixed rows and ZERO a-glyphs at bit cells
  anywhere in 266k anchors. There is NO font freedom.** The old "e at odd
  positions" observation was window cells wearing their value glyphs; the
  borrow-window a's are window-cell VALUES (w=2), not fonts. Wrong in the
  best way: SPELL(ν) has no free parameters at all.

- **P-2026-08-14-b** (SPELL(ν); registered after the font fit and manual
  calibration dumps, before running tools/spell.mjs validation): the full
  left tape at every anchor ν ≥ 34 is EXACTLY
  preamble(era) · resFont^R(ν) · zone(ν) · f^1 e^(ν−2) O^1, RLE-coalesced,
  where zone cell i (right-to-left) = cell 0 const O, cells i≡1 mod 3 =
  bit glyph (O/f) of bit@2^0 (i=1) or bit@2^(4m+4) (i=3m+4), cells 3m+2 /
  3m+3 = window glyph [O,e,a,f] of ⌊ν/2^(4m+1)⌋ / ⌊ν/2^(4m+2)⌋ mod 4;
  zone length = 5 + #pays − #borrows; R(ν) = 202 − #pays + #borrows;
  reservoir font e/a flips at even-k respells; preamble = finite per-era
  table (8 entries over the observed range). No adolescence overrides
  needed: the const-f/const-O phases ARE the window values on those eras,
  and "merge" is nothing but RLE coalescing of the deepest zone run with
  the reservoir. Expect 100.000% of anchors exact; plausible failure mode:
  off-by-one timing at the 22 event anchors themselves.
  **GRADED: ✓ EXACT — 266,351/266,351 anchors (ν ∈ [34, 266384]),
  including every event anchor, borrow gap, and both partial end eras.
  SPELL(ν) is total and perfect over the machine's whole observed life.**

- **P-2026-08-14-c** (per-lemma preservation, M2 step 3; registered before
  building/running tools/preserve.mjs). The checker: phase 1 replays every
  transition with the simulator OUT of the loop — host configs built from
  SPELL(ν), advanced by first-match book application, compared to
  SPELL(ν+1). Phase 2 measures, per fired lemma, its window reach in ν-bits
  (d_eff = 1 + highest bit any in-window zone cell reads), residue purity
  at d_eff, and class density per calendar interval. Phase 3 re-runs each
  (lemma, interval) pair ONCE symbolically with the tail e-run count formal
  (ν = r + 2^d·T, T free) and demands exact run-list equality with
  SPELL(ν+1). Predictions:
  1. Phase 1: **266,350/266,350 exact** — forced by (book replay ≡ anchors)
     ∧ (SPELL ≡ anchors), but now established TM-free.
  2. Phase 2: every non-event ∀-lemma is residue-pure at its own window
     reach, d_eff ≤ 20, and dense in its class within each interval;
     reservoir-touching windows are confined to event lemmas + the
     merged-deep-carry family.
  3. Phase 3: **100% of (∀-lemma, interval) pairs with ≥ 2 firings pass**
     the symbolic identity — an affine map agreeing with an affine target
     at ≥ 2 points is that target, and phase 1 supplies the points. Pairs
     with 1 firing stay concrete pins. If anything fails, it will be
     run-structure instability (a coalescing boundary migrating through
     the window mid-interval), surfacing as a phase-2 density break rather
     than a phase-3 algebra mismatch.
  Corollary if all pass: SPELL(ν) ⊢_book SPELL(ν+1) for every ν in every
  observed class, with the ∀ carried per class by purity ∧ density ∧
  (reach ≤ depth) ∧ symbolic identity — α-preservation + closure over the
  working book. The remaining gap to ∀-time is era generalization
  (k-induction over the calendar), which is step 4's job.

  **GRADED (tools/preserve.mjs, same day):**
  1. ✓ **266,349/266,349 exact** (the predicted denominator 266,350 was an
     off-by-one in counting the interval; the substance — 100%, TM-free —
     holds). 496 distinct lemmas fire over ν ∈ [34, 266382].
  2. Partial ✗→✓: purity-at-own-reach held for only **215/292** multi-use
     lemmas as predicted-defined. The 77 failures are the parametric
     deep-carry lemmas — their windows BIND a run count formally, so each
     fires on a FAMILY of residue classes, one per binding. Regrouped by
     binding tuple: **320/320 groups pure** at their group reach. Density:
     291/292; the single break (lemma 1927, class 767 mod 4096) is a tile
     BOUNDARY, not a hole — 1927 and sibling 1892 alternate strictly on the
     two mod-8192 sub-classes (verified by direct probe), both preserving.
     Prediction 2's failure-mode guess ("instability surfaces as a density
     break, not an algebra mismatch") was exactly right in kind.
  3. ✓ **100%: 1,982/1,982** (lemma, interval) pairs exact with the e-run
     count formal, plus **741/741** (interval, binding-group) pairs for the
     parametric lemmas. Zero algebra mismatches anywhere. 204 single-use
     lemmas + 1,663 single-firing pairs stay concrete pins (events and
     era-locals; step 4's k-induction generalizes them).
  **M2 STEP 3 SEALED**: the working book preserves SPELL — every observed
  transition is SPELL(ν) → SPELL(ν+1) by first-match lemma application
  with the simulator out of the loop, and every multi-firing class carries
  its ∀T by a machine-checked affine identity, not extrapolation.

- **P-2026-08-14-d (THE PREAMBLE LAW — C4 resolved; registered while the
  j=32 chain is still running, whose final collapse will grade it).**
  Decode of all 15 observed preamble states (chain logs j=16..30 + SPELL
  table + dumpcfg ν=6..33): the preamble is a fixed-width 8-cell numeral
  spelling **s = ⌊log₄ ν⌋** — s = k/2 where 2^k is the latest even-k
  respell; it ticks at every respell, once per generation-pair. Cell
  dialect, right to left (c0 rightmost, head c7 = const a):
  - c0 = bit0(s) in x-font {O, e}
  - c1 = bit1(s) in y-font {O, a}
  - c2 = window bit1 + 2·bit2 (full alphabet O,e,a,f — overlaps c1's bit,
    the same gearbox redundancy as the zone)
  - c3 = bit3(s) in bit-font {O, f}
  - c4..c6 = bits ≥ 4, all O so far (dialect not yet observed)
  Verified exact on every state s = 1..15: aO⁶e (s=1), aO⁴eaO (s=2),
  aO⁴eae (3), aO⁴aO² (4), aO⁴aOe (5), aO⁴faO (6), aO⁴fae (7), aO³fO³ (8),
  aO³fO²e (9), aO³feaO (10), aO³feae (11), aO³faO² (12), aO³faOe (13),
  aO³f²aO (14), aO³f²ae (15) — the "head carry" at j=28 was just bit3
  turning on (s=14 = 1110₂). bit0(s) IS the respell-type alternation
  (k≡0 vs k≡2 mod 4) and the reservoir-font phase — the register's low
  bit drives the calendar's visible alternations. The machine is a
  three-storey odometer: tail counts ν in unary, zone counts ν in binary,
  preamble counts ⌊log₄ ν⌋ in binary. Predictions:
  1. **j=31 collapse** (ν=2³¹, no respell): preamble `a O³ f² a e`
     (s=15), reservoir font a, zone O²⁴, M-offset −11.
     **GRADED mid-run: ✓ EXACT on all four components** (chain line:
     `1011^1 1010^3 1111^2 1011^1 1110^1 1011^n0-11 1010^24 …`), and the
     P-2026-08-13-b coefficient for j=31 is also exact
     (34358951936 = 2^18·131069). Prediction 2 (the s=16 carry) pending.
  2. **j=32 collapse** (ν=2³², respell k=32, s: 15→16, a 4-deep carry):
     low four cells all clear, c4 lights for the first time. Primary
     guess: c4 = window(bits 4,5) continuing the zone lattice at shift −1
     (c3 ~ zone cell 4 pattern) → glyph e → preamble **`a O² e O⁴`**.
     Alternates, in order: `a O² a O⁴` (y-font carry cell), `a O² f O⁴`
     (plain bit cell). Reservoir font flips a→e, zone O²⁵, M-offset −12.
  3. Future j=33/34 run: j=33 unchanged (s=16); j=34 respell → s=17 =
     `a O² ? O³ e` with the same c4 glyph as (2).
  4. **Capacity corollary**: if c4..c6 hold bits 4..7 zone-style (3 cells
     per 4 bits), the register holds s ≤ 255 ⇒ k ≤ 510 — the preamble
     never needs to grow before the endgame at k ≈ 275. The 4th register
     rides to M-bottom at fixed width.

- **P-2026-08-14-e** (M2 step 4 phase A — steps as class arithmetic;
  registered before building/running tools/gentheorem.mjs). With SPELL +
  preservation sealed, per-generation step counts should reduce to sums
  of affine functions over the residue classes. Predictions:
  1. **Book steps ≡ simulator steps per sweep, 0 mismatches** over all
     transitions ν ∈ [34, 266382] — the lemmas' proven step expressions,
     applied to SPELL configs, reproduce the machine's exact step count
     with the simulator out of the loop (steps join the TM-free layer).
  2. **steps(ν) is affine in ν per (class, interval)** — exact on every
     member, not a fit (the same affine-identity mechanism as
     preservation, now read off the steps coordinate).
  3. **Generation sums close**: Σ steps over each full observed
     generation [2^j, 2^{j+1}), j = 6..17, computed from the per-class
     affine formulas (α_c·Σν + β_c·#members), equals the simulator total
     exactly.
  4. **Doubling structure**: classes at depth d < j contribute member
     counts 2^(j−d) that double with j; the non-doubling residual of
     S_{j+1} − 2·S_j is confined to the event + deepest-carry classes —
     the class-level seed of the observed c' = 2c + 3·2^18 recursion,
     to be derived symbolically once phase A is green.

  **GRADED (tools/gentheorem.mjs, same day):**
  1. ✓ **266,349/266,349** — book steps ≡ simulator steps at every sweep.
     The step count is now fully inside the TM-free layer.
  2. ✓ **1,982/1,982** multi-member classes exactly affine in ν (1,045
     singletons concrete).
  3. ✓ **12/12 generations exact** (j = 6..17): Σ over each generation of
     the per-class affine formulas equals the simulator total to the step.
     The generation step count IS class arithmetic.
  4. ✓-with-refinement: every non-doubling residual j→j+1 is structured —
     either an event/newborn singleton (0→1) or a carry-boundary
     near-double (2n±1) on the workhorse ladder lemmas; no chaotic
     residuals anywhere. Exactly the boundary-term shape the
     c' = 2c + 3·2^18 recursion requires. Symbolic derivation (era
     self-similarity, period 4 in k) = phase B, pending the j=32 grades.

- **P-2026-08-14-f** (M2 step 4 phase B — era self-similarity; registered
  before building/running tools/selfsim.mjs). The ∀j induction needs the
  class table to be era-periodic. Predictions:
  1. **Era-independence of the workhorses**: every multi-use lemma that
     does not touch the reservoir has ONE (α, β) steps form — identical
     across every interval it fires in, all eras.
  2. **Reservoir-touchers are R-affine**: lemmas whose window includes the
     reservoir run have constant α and β affine in the era's R with a
     constant integer slope (the per-block crossing cost) — β = β0 + βR·R,
     same βR across all intervals of that lemma.
  3. **Period-4 fingerprints**: comparing generation j to j+4, the
     era-independent classes scale exactly ×16 in member count (up to the
     same ±O(1) carry-boundary corrections seen in phase A), and the
     era-specific residual lemmas of generation j+4 correspond
     one-for-one to those of generation j (same count pattern, deeper
     scale) — no new kinds of behavior appear with k.
  4. **Second difference law**: D_j := S_{j+1} − 2·S_j obeys
     D_{j+4} = 16·D_j + (era constant), the absolute-total shadow of
     c' = 2c + 3·2^18.

  **GRADED (tools/selfsim.mjs, same day):**
  1. ✓ **BETTER than predicted: 182/182** lemmas firing in ≥2 intervals
     have ONE (α, β) — constant across every interval and era, no
     exceptions, including the reservoir-touchers.
  2. Moot (subsumed by 1): ZERO lemmas needed an R-affine β. Ordinary
     sweeps never pay an R-dependent crossing cost; the only R-sensitive
     sweeps are the per-era event singletons.
  3. Partial ✓: the ×16-exact core grows steadily (11 → 138 lemmas by
     j=13→17) with the predicted ±O(1)-per-boundary band around it; every
     residual is a class BIRTH (0→n, n ∈ {1,4,8} — deeper classes
     activating as j grows), zero deaths, zero chaotic changes. The
     1:1 skeleton correspondence of newborns across periods remains to be
     mechanized (skeleton mapping, next build).
  4. ✗ as formulated — wrong observable: raw totals have a 4^j leading
     term, so D_j ≈ 4·D_{j−1}, not 16·D_{j−4} + const. The corrected law
     the data forces: **E_j := D_{j+1} − 4·D_j alternates between two
     near-constants (period 2: ≈ −9.5k, +14.3k)** — i.e.
     S_j = A·4^j + B_p·2^j + C_p with p-periodic lower coefficients.
     Era self-similarity confirmed at the totals level in corrected form;
     the c' = 2c + 3·2^18 recursion lives in the N-coefficient and needs
     the symbolic split S_j(n0, n1) — next build alongside the skeleton
     map.
  **Phase B status: the class table is era-INVARIANT for the entire
  multi-use book (stronger than self-similar — the same finite rulebook
  with the same step forms serves every era; only the event singletons
  and class-birth schedule carry k-dependence). The ∀j induction now
  reduces to: (a) the class-birth schedule as a function of k (the
  calendar, already formulaic), (b) skeleton correspondence of event
  singletons across periods, (c) the N-coefficient recursion from the
  symbolic sum. All three are finite checks over structures already in
  hand.**

- **P-2026-08-14-g** (phase B part 2 — the N-coefficient theorem;
  registered before building/running tools/ccoef.mjs). Each sweep's step
  cost is α·ν + β; in a formal-N chain the generation's N-coefficient is
  therefore Σα over the generation's sweeps, where each lemma's α can be
  read directly off its PROVEN step expression (the coefficient of the
  e-run parameter) — no fitting. Predictions:
  1. **Book α ≡ fitted α**: for every multi-member class, the affine
     slope fitted from concrete steps equals the e-run coefficient in the
     lemma's symbolic steps expression. 0 mismatches.
  2. **Σα_j = 2^(j+4) exactly** for every full observed generation
     (j = 7..17). External anchors at both ends: the epoch-3 theorem's
     N-coefficient 1024 = 2^10 (j=6) and the chain table's cumulative
     diffs 2^(j+4) (j = 16..17).
  3. **Pure doubling with exact cancellation**: Σα_{j+1} − 2·Σα_j = 0,
     i.e. the α-weighted boundary corrections (the 2n±1 classes and
     newborns) cancel exactly each generation — this is the class-level
     mechanism of the c' = 2c + 3·2^18 recursion (whose +3·2^18 lives
     purely in the cumulative composition, since exact diff-doubling ⇔
     that recursion).
  4. **Singles census**: the single-firing classes collapse into skeleton
     families whose firing ν's form geometric ladders (consecutive ratios
     ∈ {2, 4, 16}), covering ≥90% of singles — the event lemmas are
     periodic families, not sporadic behavior.

  **GRADED (tools/ccoef.mjs, same day):**
  1. ✓ **1,982/1,982** — every multi-member class's fitted slope equals
     the e-run coefficient of the lemma's proven steps expression. α is
     now read off the book, not measured.
  2. ✓ **Σα_j = 2^(j+4) EXACT, all 11 full generations (j=7..17)** —
     matching the epoch-3 theorem (2^10 at j=6) and the chain table's
     diffs at j=16..17. **THE N-COEFFICIENT THEOREM: the per-generation
     N-coefficient is 2^(j+4), and its exact doubling IS the
     c' = 2c + 3·2^18 recursion in cumulative form.** C1's mechanism is
     now derived from the class table instead of conjectured from fits.
  3. ✓ Σα_{j+1} − 2·Σα_j = 0 exactly, every generation — the α-weighted
     boundary corrections cancel identically. (Where a 2n±1 class loses a
     member, sibling classes gain matching α; the cancellation is
     class-level bookkeeping, ripe for a per-calendar-position proof.)
  4. ✗ as formulated — the singles are NOT geometric ladders in raw ν:
     they all fire at ODD ν. They are sparse deep-carry classes with one
     member per interval (including the event-crossing sweeps at
     ν = 2^k−1, 3·2^k−1, …), organized by trailing-ones depth and
     calendar-relative position, in just **28 skeleton families**. The
     correct correspondence key for the induction is (skeleton,
     carry-depth class, interval type) — next build. The narrowness (28
     kinds for 1,045 firings) strongly supports finite k-parametrization.

- **P-2026-08-14-h** (phase B part 3 — skeleton k-parametrization;
  registered before building/running tools/skeleton.mjs). The last ∀j
  ingredient: each of the 28 singles skeleton families is one
  k-parametrized law, not sporadic instances. Predictions:
  1. **Affine depth model**: ≥ 24 of 28 families satisfy
     steps = α·ν + γ·t + δ (t = trailing-ones(ν); α, γ, δ per family)
     EXACTLY, fitted on 3 members and verified on all others. Failures,
     if any, split by a small-power-of-2 residue of ν into exact
     subfamilies (carry-phase branches).
  2. **Position ladder**: within each family (or split subfamily),
     writing ν+1 = q·2^a (q odd), q takes ≤ 4 distinct values and there
     is exactly ONE firing per (q, a) slot — each family is a clean
     ladder in a, i.e. a single law marching up the scales with k.
  3. Corollary if 1+2 hold: the complete generation composition is
     finitely presented — era-invariant classes (182 forms) + calendar
     (formulaic) + 28 parametrized singleton families — and the ∀j
     induction closes over this finite presentation.

  **GRADED (tools/skeleton.mjs, same day):**
  1. ✗ as registered, ✓ refined — the (ν, t)-affine model fails
     everywhere; the data forced two corrections, each structural:
     (a) the depth term is **γ·t + γ₄·⌊t/4⌋** — the 3-cells-per-4-bits
     lattice appearing in the crossing cost (a carry of depth t crosses
     the staircase of cells, not raw bits); (b) the even-k respell
     collapses (ν = 2^k−1, k even) cost a **flat 1680 steps regardless
     of era** — the full-reservoir re-spell, whose cost the M+K
     conservation law holds constant while R and len drift. With the
     lattice term + respell interaction: **22/23 testable families pass
     whole (margins up to 156 held-out rows), 1 exactly-determined
     (n=4, consistent, unverifiable), 0 refuted.** 20 of 22 need NO era
     regressors at all — the singles' step laws are era-free.
  2. ✗ — q-sets are rich (odd parts of ν+1 are unbounded co-factors);
     but the position law is SUBSUMED: singles are (lemma, interval)
     classes, and their firing positions already follow from the step-3
     residue classes. No separate position law exists or is needed.
  3. ✓ in refined form: **the complete generation composition is
     finitely presented** — 182 era-invariant workhorse forms + the
     formulaic calendar + 28 singleton families with lattice-affine
     era-free laws (+ one era-invariant respell constant). This is the
     finite presentation the ∀j induction closes over.

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

**α value-congruence status (tools/alpha.mjs, session 5 cont.):** the
reservoir-phase hypothesis was tested and DIED (graded ✗ — conditioning
deep-a's value on the reservoir font made the congruence worse). The
necropsy found the truth, per-position conditional stats (restricted to
non-truncated zones), zero exceptions at p4–p6:

- **The a-digit is a ZERO.** Deep-cell value map: {O, a} = 0, {e, f} = 1.
  Four glyphs, two values. `a` (=1011) is a zero written in a
  token-heavier font: it carries budget WITHOUT carrying value — the
  exact point where the conserved quantity (tokens/extent) and the
  counted quantity (ν) decouple. No debt VALUES exist in the zone; debt
  is pure spelling + reservoir accounting.
- **Sliding cells unchanged:** p2 = ⌊v/2⌋ mod 4, p3 = ⌊v/4⌋ mod 4 with
  the full 4-symbol alphabet as window VALUES (a=2 legitimately there).
- **Collapse mechanics watched live** (ν=512, 1024 dumps): at a PAYING
  collapse (ν=2^9), the reservoir count drops by 1 and the zone grows one
  cell — the payment is a single block moving reservoir → zone, extent
  conserved. At a NON-paying collapse (ν=2^10), the zone length stays and
  the ENTIRE reservoir re-spells 1110^199 → 1011^199 — the reservoir font
  flip IS the generation-pair alternation observed since session 1.
- **The cell calendar (tools/cells.mjs; EXACT — only 22 zone-size/font
  events in the machine's whole observed life, all at ν ∈ {1,3,5}·2^k):**
  period 4 in k: k≡0 → reservoir re-spells a→e at ν=2^k (no exchange);
  k≡1 → PAY (+1 cell, reservoir −1) at 2^k AND at 3·2^k; k≡2 → re-spell
  e→a at 2^k, PAY at 3·2^k, BORROW (−1 cell, reservoir +1) at 5·2^k;
  k≡3 → PAY at 3·2^k only. Net per 4 generations: 4 pays − 1 borrow =
  reservoir −3 — the drain law DERIVED. Zone size is a pure step function
  of this calendar, not of the count's bit-length.
- **The tiered frame (verified over ALL 266,351 anchors, 0 exceptions):**
  cell p_i laws, fixed for the machine's entire observed life —
  p0/p1 head-phase; p2 = ⌊ν/2⌋ mod 4; p3 = ⌊ν/4⌋ mod 4 (gearbox pair 1,
  overlapping windows over bits 1–3); p4 = bit4(ν); p5 = ⌊ν/32⌋ mod 4;
  p6 = ⌊ν/64⌋ mod 4 (gearbox pair 2, bits 5–7); p7 = bit8(ν);
  p8 = bit9(ν). Single-bit cells use font {O,a}=0, {e,f}=1. The gearbox
  scales (2^1/2^2, 2^5/2^6) sit at period 4 in the exponent — the SAME
  period as the pay calendar: the machine installs a gearbox where the
  carry traffic is, one tier per calendar period.
- **THE COMPLETE LATTICE (tools/frontier.mjs; per-era fits, settled laws
  exact in every era from settling onward, tiers m = 0..3 all verified):**
  cell 3m+2 = window ⌊ν/2^(4m+1)⌋ mod 4; cell 3m+3 = window
  ⌊ν/2^(4m+2)⌋ mod 4; cell 3m+4 = bit_{4m+4}(ν) (font {O,a}=0, {e,f}=1).
  **Three cells per four bits — the −3-per-4-generations reservoir drain
  IS the information rate of the encoding.** Window-cell symbols are fully
  value-determined; bit-cell FONTS are the only freedom, and that freedom
  is where the budget ink lives (finite overlay, still to map).
- **Frontier adolescence, identical at every tier (period-4 shifted):** a
  window cell born at the 3·2^k pay spells `const f` until the next
  collapse, `const O` until the borrow, VANISHES during the borrow gap
  (the borrowed cell is the newest one — the K-stall law in the flesh),
  is re-bought at the next pay, then settles into its window law
  permanently. Observed identically for cell 6 ([192,384)), cell 9
  ([3072,6144)), cell 12 ([49152,98304)). Bit cells (4, 7, 10, 13) are
  born at the 2^k pays (k ≡ 1 mod 4) and settle instantly.
- **SPELL(ν) — SEALED (tools/spell.mjs, 266,351/266,351 anchors exact,
  the machine's whole observed life, zero exceptions):**
  SPELL(ν) = preamble(era) · resFont^R(ν) · zone(ν) · f^1 e^(ν−2) O^1,
  RLE-coalesced, with:
  - zone cell i (right-to-left): cell 0 = const O; cell 1 = bit0(ν);
    cell 3m+2 = ⌊ν/2^(4m+1)⌋ mod 4; cell 3m+3 = ⌊ν/2^(4m+2)⌋ mod 4
    (window glyphs O,e,a,f = 0,1,2,3); cell 3m+4 = bit_{4m+4}(ν) —
    bit glyphs 0 = O, 1 = f ALWAYS (no font freedom; P-2026-08-14-a).
  - zone length = 5 + #pays(≤ν) − #borrows(≤ν); R(ν) = 202 − #pays +
    #borrows; both from the calendar generated formulaically (k≡0:
    respell a→e @2^k; k≡1: pay @2^k, @3·2^k; k≡2: respell e→a @2^k,
    pay @3·2^k, borrow @5·2^k; k≡3: pay @3·2^k).
  - reservoir font: e/a, flipping at the even-k respells.
  - preamble: finite per-respell-era table, 8 entries over the observed
    range (a¹O⁴e¹a¹O¹ → a¹O⁴e¹a¹e¹ → a¹O⁴a¹O² → a¹O⁴a¹O¹e¹ → a¹O⁴f¹a¹O¹
    → a¹O⁴f¹a¹e¹ → a¹O³f¹O³ → a¹O³f¹O²e¹) — the 4th register. **DECODED
    (P-2026-08-14-d): the table is the numeral of s = ⌊log₄ ν⌋, an 8-cell
    fixed-width SPELL-dialect counter ticking at each respell; all 15
    states s=1..15 decode exactly (cell laws in §3.1). The machine is a
    three-storey odometer: ν in unary (tail), ν in binary (zone),
    ⌊log₄ ν⌋ in binary (preamble).**
  - **No adolescence overrides exist**: the const-f/const-O phases of
    newborn window cells ARE their window values on those short eras, and
    "merge" is nothing but the tape's own RLE coalescing when the deepest
    zone glyph equals the reservoir font. The entire zone is pure lattice
    whenever a cell exists at all.
- **The x/y decomposition (why there is no font freedom):** every glyph
  is the block 1x1y with x, y ∈ {0,1}: O=1010 (x0 y0), e=1110 (x1 y0),
  a=1011 (x0 y1), f=1111 (x1 y1). Window value w = x + 2y, so a window
  cell at scale s stores x = bit_s(ν), y = bit_{s+1}(ν) — its two
  physical spare bits ARE two consecutive bits of the count. A bit cell
  at scale s stores x = y = bit_s(ν) (the bit duplicated). The deep value
  map {O,a}=0, {e,f}=1 is just "read x"; ink (token count) is 2 + x + y.
  Total zone ink is therefore a pure function of ν — budget bookkeeping
  has no spelling freedom anywhere, which is exactly why M+K=207 can be
  a per-lemma theorem.
- **Per-lemma preservation — SEALED (tools/preserve.mjs, M2 step 3,
  P-2026-08-14-c):** SPELL(ν) ⊢_book SPELL(ν+1). TM-free replay exact at
  all 266,349 transitions (host configs BUILT from SPELL, advanced by
  first-match lemma, compared to SPELL(ν+1) — the simulator never runs).
  Every multi-firing (lemma, interval[, binding-group]) pair passes a
  symbolic affine identity with the e-run count formal (1,982 + 741 pairs,
  zero mismatches), so each class's ∀T is machine-checked. Class structure:
  215 lemmas residue-pure and dense at their own window reach; 77
  parametric deep-carry lemmas = 320 binding-groups, all pure; one tile
  boundary at mod 8192 (lemmas 1927/1892 alternate, complementary, no
  hole). Remaining ∀-gap: era generalization (k-induction), step 4.

## 4.5 The finite presentation and the ∀j generation theorem (M2 close-out)

**The universal cost law (2026-08-14): α = 16 for every e-formal lemma
in the book — 2,237/2,237** (135 e-pinned birth-era pins and 5 birth
shapes excluded; census over data/book.json steps expressions). Hence
every sweep costs exactly **steps(ν) = 16·ν + off(ν)**: sixteen steps
per unit counted, plus a bounded service charge. The per-generation
N-coefficient 2^(j+4) = 16·2^j is a corollary (2^j sweeps at slope 16),
and with it the c' = 2c + 3·2^18 recursion. The surcharge off(ν) is:
- workhorse classes: a per-class constant (182 era-invariant forms);
- deep-carry/event singles: γ·t + γ₄·⌊t/4⌋ + δ per skeleton family
  (28 families; t = trailing-ones(ν); the ⌊t/4⌋ term is the
  3-cells-per-4-bits lattice in the crossing cost);
- even-k respell collapses: flat +1680, era-invariant because M+K=207
  fixes the extent being re-spelled.

**G(j), the generation theorem (statement):** from the collapse anchor
at ν = 2^j — tape SPELL(2^j), preamble = numeral(⌊j/2⌋), reservoir R(j)
and zone K(j) per calendar — the machine executes exactly 2^j sweeps
ν → ν+1 (each SPELL(ν) ⊢_book SPELL(ν+1)), reaching the collapse anchor
at ν = 2^(j+1), in total steps 16·Σν + Σoff, where Σν is closed-form and
Σoff decomposes by trailing-ones depth (2^(j−t−1) members at depth t)
into geometric sums over the family laws plus the calendar's event
constants.

**Proof-status ledger (what kind of evidence each component has):**
1. PROVEN, machine-checked symbolic, ∀ params: every lemma (M1); the
   per-class preservation identities (step 3); α = 16 per lemma (read
   off the proven step expressions, not measured).
2. VERIFIED-EMPIRICAL, exact, zero exceptions over 12 full generations
   (266,349 sweeps) + symbolic chain to j=31 (~10^18 steps): the
   calendar; the class-birth schedule; era-invariance of the 182 forms;
   the 28 family lattice laws; the constant respell charge; the
   preamble register law (s = 1..15).
3. REMAINING FORMAL GAP (the busycoq work list): (a) class-birth
   schedule ∀k — derivable from the SPELL definition per k mod 4;
   (b) family lattice laws ∀t — currently t ≤ 18; carried by the
   parametric deep-carry lemmas' formal run counts, one algebraic
   identity per family; (c) preamble transition ∀s — verified s ≤ 15,
   s = 16 prediction pending the j=32 chain.

M3 is unblocked in practice: composing G(j) from j=16 to M-bottom
(j ≈ 275) requires only this presentation + calendar arithmetic; the
endgame configuration can be constructed and run concretely while the
formal-gap items are ported.

## 4.6 Segment-map findings (why the induction lives on the numeral)

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
- `node tools/lemmas.mjs` — milestone-1 rulebook (1,541 lemmas, 100.000%).
- `node tools/lift.mjs` — ∀-form lift; writes data/book.json (the working book).
- `node tools/compose-test.mjs` — 266,383 transitions by pure composition.
- `node tools/audit.mjs` — per-lemma N+1 and extent-conservation (0 exceptions).
- `node tools/cells.mjs` — the 22-event cell calendar.
- `node tools/frontier.mjs` — per-cell per-era lattice fits (data/frontier.txt).
- `node tools/decode.mjs`, `tools/alpha.mjs` — decoder development probes
  (historical; the settled laws live in §4.4).
- `node tools/font.mjs` — bit-cell font fit (0=O, 1=f, zero freedom).
- `node tools/spell.mjs` — SPELL(ν) + validation (266,351/266,351 exact).
- `node tools/dumpcfg.mjs [ν...]` — dump full anchor configs at chosen ν.
- `node tools/preserve.mjs` — M2 step 3: per-lemma preservation
  SPELL(ν) ⊢_book SPELL(ν+1), TM-free replay + symbolic class identities.
