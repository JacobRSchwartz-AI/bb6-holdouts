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

| j  | N = 2^j−2 | K  | M offset | steps coefficient of N | constant term |
|----|-----------|----|----------|------------------------|---------------|
| 16 | 65534     | 13 | M        | 2^18·1                 | 2148554104    |
| 17 | 131070    | 14 | M−1      | 2^18·5                 | 53692443344   |
| 18 | 262142    | 14 | M−1      | 2^18·13                | 362938652012  |
| 19 | 524286    | 15 | M−2      | 2^18·29                | 1806064790212 |
| 20 | 1048574   | 16 | M−3      | 2^18·61                | 7990851949928 |

(steps measured from the N=49150 anchor with M=194 formal; templates in
tools/factory.mjs output, committed.)

### 1.3 Composed mega-theorem
For all M ≥ 4, N ≥ 1: from the epoch-13 start config (N-run = N, M-run = M),
the machine reaches the generation-20 collapse config (M-run = M−3, N-run =
N+999424) in exactly 24M + 15990784N + 7990851949928 steps.

## 2. Verified-empirical invariants (exact over observed range, no ∀-proof yet)

- **Budget invariant**: M + K = 207 at every collapse anchor observed
  (j=16..20 symbolically; every anchor of the machine's first 8.9×10^13
  steps concretely, via the epoch logger).
- N increments by exactly 1 per anchor visit (concrete, full observed range).
- M's offset is non-monotone: a transient +1 borrow occurred at
  N ∈ [81918, 98302) inside generation 17.

## 3. Conjectures

- **C1 (coefficient recursion)**: the steps N-coefficient of generation j is
  c_j = 2^18·(2^(j−14) − 3)  — equivalently c'=2c+3·2^18; verified j=16..20,
  predicts c_21 = 2^18·125, c_22 = 2^18·253, c_23 = 2^18·509, c_24 = 2^18·1021.
- **C2 (collapse cadence)**: collapse anchors occur at every N = 2^j − 2,
  j ≥ 16 (and an analogous pre-2^16 cadence with odd multipliers).
- **C3 (budget)**: M + K = 207 at every collapse anchor, for the machine's
  entire life.
- **C4 (preamble register)**: the runs left of the M-run form a bounded
  numeral ("preamble register") ticking once per generation; it determines
  when M pays vs borrows, and generates the {5,3,1,3,3,1,...} odd-part
  pattern of the pre-2^16 era.
- **C5 (endgame)**: M drains on average ~3 per 4 generations; M-bottom
  (K→207) at roughly generation ~200, i.e. ~10^126 steps, where the halt
  transition (D,0) may become reachable. The machine's fate is decided there.

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
