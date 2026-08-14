# Submission draft: the Odometer (BB(6) holdout) halts

**Machine:** `1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA` ("the Odometer")
**Claim:** the machine HALTS, after ≈ 8·(19·2^279)² ≈ 2^569.5 ≈ 10^171.4
steps. It should move from the BB(6) holdout list to the halting column.
**Authors:** Jacob Schwartz (direction, prediction-first protocol, the
empirical campaign) and Claude (Anthropic) — joint work.

## Where to submit, in order

1. **bbchallenge Discourse** (discuss.bbchallenge.org) — new topic in
   the "Individual machines" category: the informal argument + the
   evidence chain + link to the repo. This is where holdout analyses
   are reviewed by the community (precedent: Skelet #1, #17, #33
   threads).
2. **busycoq PR** (github.com/meithecatte/busycoq) — once the full
   `halts tm c0` certificate is closed: add `BB62.v`, `Individual62.v`,
   `Odometer.v`, `OdometerDip.v` (+ the orbit/base files) to
   `verify/`, wire into the Makefile. Note: busycoq is non-halt
   focused; a halt certificate may belong in bbchallenge's proof
   repositories instead — ask in the Discourse thread first.
3. **bbchallenge wiki / holdouts list** — after review, the machine's
   status entry is updated with links to the thread + certificate.

## The discovery story (for the Discourse post)

- An informal non-halt argument ("the stationary meta-cycle") survived
  100M-step censuses, exact clock validation over ~10^5 sweeps, and
  seeded runs at v jumps up to 2^212 and winters at 2^283 — and was
  WRONG. The winter seeds were built from a spelling formula whose
  boundary assumption the real orbit breaks exactly once, at
  v = 2^282−1 — an event no simulation had ever crossed.
- The flaw was found in minutes by a closure test written WHILE
  FORMALIZING the argument in Coq: dip(spell v) = spell(v+1) fails at
  exactly one value per era. Formalization did what testing could not.
- The corrected orbit: the boundary decays geometrically (inner a spent
  at v=2^282−1, cascade, single outer a) and the machine halts at
  v = 2^283 after the crisis at ν = 3·2^279 — total ν_death = 19·2^279
  sweeps.

## Evidence chain (all in the repo, reproducible)

| Claim | Verification |
|---|---|
| Block-level abstract machine ("the dip") ≡ raw TM | 5999/5999 anchors (tools/dipwalk.mjs); census of ALL block transitions sealed over 100M raw steps (tools/census.mjs) |
| Toy odometers (same structure, small zones) halt at 2^(4G+3) sweeps | RAW simulation: width 6 halts at step 154,134; width 9 at step 33,925,642 — abstract machine anchor-exact throughout |
| Width-213 (real) exception at v=2^282 | Macro sim, in-run crossing (tools/exception213.mjs) |
| Width-213 death at v=2^283 | Macro sim from derived pre-death structure: HALT (tools/death213.mjs) |
| Pre-crisis history (structured era, descent, crisis) | M1–M3 campaign: 1,541-lemma sealed rulebook, chain prover to j=32 with 4/4 blind predictions exact, descent ledger, endgame cascade (notes/odometer.md) |

## The Coq certificate (busycoq-based, Coq 8.18, zero axioms)

Proved and machine-checked today (`coq/`, build: tools/coq-build.sh):
- `dip_go_sound` — the abstract dip machine IS the TM (every walk step
  = real tape steps; one block lemma per census rule).
- `sweep_theorem` — the universal sweep: dip success ⇒ anchor advances.
- `dip_go_dies_sound` + `death_sweep` — a dying dip ⇒ the machine halts
  (D reads blank after the walk crosses the spent boundary).
- `dip_iter_sound` + `halts_of_orbit_death` + **`halts_c0_of`** — the
  assembled theorem: reachability + orbit-death ⇒ `halts tm c0`.
- **`toy6_halts`** — COMPLETE unconditional halting proof of the width-6
  toy: its 127-sweep orbit computed by vm_compute inside Coq, the fatal
  sweep verified to the halt transition. `Print Assumptions`: closed.

Remaining obligations for the full `halts tm c0` (both mechanical in
design, work in progress):
1. **Base:** `c0 -->* anchor W_base n_base` via Compute.v's certified
   `cmultistep` + vm_compute (~353k steps across the early era).
2. **Orbit:** `dip_iter N (W_base) = Some W_pre` with `dip_dies W_pre`
   for explicit N ≈ 19·2^279 — by acceleration lemmas over the spelling
   families (structured era ledger + regime-3 counter + decay cascade),
   pure computation about the dip function, no tape reasoning.

Also planned: exact N_halt (a ~172-digit integer) from the validated
step-count clock.

## Checklist before posting (Jacob signs off on each)

- [ ] Full `halts tm c0` closed in Coq (obligations 1–2 above)
- [ ] Clean-clone build verified from scratch
- [ ] Exact N_halt computed and cross-checked
- [ ] Discourse post drafted from this file, reviewed by Jacob
- [ ] Repo public (or archive attached), README with build instructions
- [ ] Attribution line as above approved by Jacob
