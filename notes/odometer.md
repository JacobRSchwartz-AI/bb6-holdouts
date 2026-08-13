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

## 5. Reproduction

- `node tools/validate.mjs` — simulator exactness (BB(2)–BB(5) step counts).
- `node tools/chain.mjs 30 64 202` — epoch-3 theorem.
- `node tools/factory.mjs 49150 1100000 194 8000000` — generations 16–20.
- `node tools/epoch.mjs 50000000` — concrete epoch table from birth.
