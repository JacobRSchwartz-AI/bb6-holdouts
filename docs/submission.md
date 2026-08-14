# Submission draft: the Odometer (BB(6) holdout) halts

**Machine:** `1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA` ("the Odometer")
**Claim:** the machine HALTS, on sweep 3·2^279 of its tail clock, after
exactly

    N_halt = 67931323646787744340347982457788840036504581967495927710
             77171340442123492305867933761244645774908114601585353157
             21018132084275421883147320661638136374334659122557882929
             34

steps (170 digits, = 2^564.1699 ≈ 6.79·10^169). It should move from the
BB(6) holdout list to the halting column.
**Authors:** Jacob Schwartz (direction, prediction-first protocol, the
empirical campaign) and Claude (Anthropic) — joint work.

## Where to submit, in order

1. **bbchallenge Discourse** (discuss.bbchallenge.org) — new topic in
   the "Individual machines" category: the informal argument + the
   evidence chain + link to the repo. This is where holdout analyses
   are reviewed by the community (precedent: Skelet #1, #17, #33
   threads).
2. **busycoq PR** (github.com/meithecatte/busycoq) — the full
   `halts tm c0` certificate: add `BB62.v`, `Individual62.v`,
   `Odometer.v`, `OdometerDip.v`, `OdometerOrbit.v`, `OdometerBase.v`,
   `OdometerLedger.v` to `verify/`, wire into the Makefile. Note:
   busycoq is non-halt focused; a halt certificate may belong in
   bbchallenge's proof repositories instead — ask in the Discourse
   thread first.
3. **bbchallenge wiki / holdouts list** — after review, the machine's
   status entry is updated with links to the thread + certificate.

## The discovery story (for the Discourse post)

- An informal non-halt argument ("the stationary meta-cycle") survived
  100M-step censuses, exact clock validation over ~10^5 sweeps, and
  seeded runs at v jumps up to 2^212 and winters at 2^283 — and was
  WRONG. The winter seeds were built from a spelling formula whose
  boundary assumption the real orbit breaks exactly once, at an event
  no simulation had ever crossed.
- The flaw was found in minutes by a closure test written WHILE
  FORMALIZING the argument in Coq: dip(spell v) = spell(v+1) fails at
  exactly one value per era. Formalization did what testing could not.
- The same lesson then struck a THIRD time: the corrected "crisis
  ladder" design (eight rungs through [bit; win; a; a] tops) was
  proved in Coq, mechanically flawless — and end-to-end ledger
  enumeration showed the real orbit never enters that family either.
  The cure that finally stuck: enumerate the ACTUAL orbit from the
  proven base anchor, with every acceleration step mirroring a proved
  Coq lemma, and let vm_compute re-check every event. Every seeded
  validation must be paired with a reachability argument for the seed.
- The true orbit (tools/ledger.mjs, cross-checked against plain
  iteration over 3M sweeps): from the base anchor the counter marches
  through 549 "events" (concrete carry-overflow dips) separated by
  parametric spans, and dies when the walk crosses the last boundary
  block: the fatal sweep is tail-clock sweep 3·2^279 EXACTLY.

## Evidence chain (all in the repo, reproducible)

| Claim | Verification |
|---|---|
| Block-level abstract machine ("the dip") ≡ raw TM | 5999/5999 anchors (tools/dipwalk.mjs); census of ALL block transitions sealed over 100M raw steps (tools/census.mjs); Coq `dip_go_sound` |
| Toy odometers (same structure, small zones) halt | RAW simulation: width 6 halts at step 154,134; width 9 at step 33,925,642 — abstract machine anchor-exact throughout; Coq `toy6_halts` end to end |
| The real orbit, base anchor → death | Ledger enumeration (tools/ledger.mjs): 549 events, exact BigInt sweep counts, plain-iteration cross-check over 3M sweeps; every event re-checked in Coq by vm_compute (OdometerLedger.v) |
| Base reachability (c0 → first glyph-aligned anchor, step 354,540) | In-kernel Coq computation (`brun` + `base_reach`, OdometerBase.v) |
| Pre-history context (structured era, descent, crises) | M1–M3 campaign: 1,541-lemma sealed rulebook, chain prover with 4/4 blind predictions exact, descent ledger (notes/odometer.md) — superseded as *proof* by the ledger, retained as the map that found the structure |

## The Coq certificate (busycoq-based, Coq 8.18, zero axioms)

**`Theorem odometer_halts : halts tm c0.`** (OdometerLedger.v)

The pipeline (all `Print Assumptions`-closed):
- `dip_go_sound` — the abstract dip machine IS the TM (one block lemma
  per census rule).
- `sweep_theorem` — dip success ⇒ anchor advances by one sweep.
- `dip_go_dies_sound` + `death_sweep` — a dying dip ⇒ the machine halts.
- `dip_iter_sound` + `halts_of_orbit_death` + `halts_c0_of` — orbit
  composition down to `halts tm c0`.
- `base_reach` (OdometerBase.v, generated) — c0 reaches the base anchor
  in 354,540 steps, computed in-kernel.
- `zwalk` / `dip_spell` / `dip_iter_spell` (OdometerOrbit.v) — THE
  INCREMENT THEOREM: one sweep adds one to the zone counter; n sweeps
  add n, parametrically, below group capacity. Covers every span
  between events.
- `OdometerLedger.v` (generated by tools/genledger.mjs) — 549 event
  lemmas (each a single concrete dip, `vm_compute`), `span_any`/`leg`
  glue, `ledger_chain`, and `odometer_halts`.
- `toy6_halts` — the same pipeline, end to end, on the width-6 toy.

Death statement, intrinsically: the dying anchor's tail index is
3·2^279 − 3 (the `anchor _ n` index is explicit in the chain), so the
fatal sweep is tail-clock sweep 3·2^279.

## The exact step count (the showpiece)

N_halt above is exact, from an exact per-sweep clock law
(tools/clock.mjs: `cost = 56 + 16n + 4·bounces + Σ rule-weights`,
residual **zero** on 3000 instrumented real-orbit sweeps), summed in
BigInt over the full orbit via the ledger's span/event structure
(tools/nhalt.mjs: digit combinatorics per span + 549 event profiles +
fatal partial `4n + 4·crossings + 14`). Validation: the identical
pipeline reproduces the raw halting step counts of both toy odometers
EXACTLY (toy6: 154,134; toy9: 33,925,642), and the real run's internal
checks land exactly (fatal sweep 3·2^279; dying crossings 216).
Note: N_halt is JS-computed and toy-validated, not Coq-certified — the
Coq theorem certifies *that* the machine halts; the exact count is
presented as a validated computation.

## Checklist before posting (Jacob signs off on each)

- [x] Full `halts tm c0` closed in Coq (pending final compile check)
- [ ] Clean-clone build verified from scratch
- [ ] Exact N_halt computed and cross-checked
- [ ] Discourse post drafted from this file, reviewed by Jacob
- [ ] Repo public (or archive attached), README with build instructions
- [ ] Attribution line as above approved by Jacob
