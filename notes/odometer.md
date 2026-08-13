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

## 5. Reproduction

- `node tools/validate.mjs` — simulator exactness (BB(2)–BB(5) step counts).
- `node tools/chain.mjs 30 64 202` — epoch-3 theorem.
- `node tools/factory.mjs 49150 1100000 194 8000000` — generations 16–20.
- `node tools/epoch.mjs 50000000` — concrete epoch table from birth.
