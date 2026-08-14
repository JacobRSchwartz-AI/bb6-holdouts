# bb6-holdouts

Analysis of open BB(6) holdout machines
(https://wiki.bbchallenge.org/wiki/BB(6)). Node ≥22, no dependencies;
Coq 8.18 for the certificates.

## Headline result: the Odometer HALTS

`1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA` ("the Odometer"), a BB(6)
holdout, **halts** — on sweep 3·2^279 of its tail clock, after exactly

    N_halt = 67931323646787744340347982457788840036504581967495927710
             77171340442123492305867933761244645774908114601585353157
             21018132084275421883147320661638136374334659122557882929
             34

steps (170 digits, ≈ 2^564.17 ≈ 6.79·10^169).

- **Machine-checked certificate**: `Theorem odometer_halts : halts tm c0`
  in `coq/OdometerLedger.v`, built on [busycoq](https://github.com/meithecatte/busycoq)
  (Coq 8.18, zero axioms — `Print Assumptions` closed). CI
  (`.github/workflows/coq-verify.yml`) rebuilds the full chain from a
  clean busycoq clone on every push.
- **Exact step count**: JS-computed from an exact per-sweep clock law
  (residual zero over 3000 instrumented sweeps), toy-validated to the
  step on two smaller odometers; the Coq theorem certifies *that* it
  halts, the count is a validated computation. See `tools/nhalt.mjs`.
- Full claim, discovery story, and evidence chain: `docs/submission.md`.
  Working notes and the prediction-first protocol log: `notes/odometer.md`.

Authors: Jacob Schwartz (direction, prediction-first protocol, the
empirical campaign) and Claude (Anthropic) — joint work.

## Reproducing the Coq certificate

```sh
git clone https://github.com/meithecatte/busycoq
cp coq/*.v busycoq/verify/
cd busycoq/verify
coq_makefile -Q . BusyCoq -o Makefile.port \
  LibTactics.v Helper.v Pigeonhole.v TM.v Compute.v Flip.v Permute.v \
  Individual.v BB62.v Individual62.v Odometer.v OdometerDip.v \
  OdometerOrbit.v OdometerCrisis.v OdometerBase.v OdometerLedger.v
make -f Makefile.port -j1
echo 'Require Import BusyCoq.OdometerLedger. Print Assumptions odometer_halts.' \
  | coqtop -Q . BusyCoq -batch -l /dev/stdin
```

Needs ~8GB RAM (OdometerOrbit.v peaks ~7.2GB; give the machine swap
headroom). `tools/coq-build.sh` does the same inside WSL. Use `-j1`:
parallel make has raced dependent files into checksum-inconsistent
`.vo`s.

## Toolbox (general holdout hunting)

- `data/holdouts-1534.csv` — snapshot of the community tracker spreadsheet
  (1,534 list with status annotations). `data/open.txt` — the machines with
  blank status (open as of the snapshot). `data/triage.tsv` — compression
  ranking from `tools/triage.mjs`.
- `src/machine.mjs` — standard-format parser (`---` = undefined = halt).
- `src/naive.mjs` — reference simulator; only used to validate the macro sim.
- `src/macro.mjs` — the workhorse: k-cell macro blocks over an RLE tape,
  memoized in-block transitions, shift-rule acceleration (a run of n equal
  blocks crossed in the same state costs one BigInt multiply). Emits two
  non-halt certificates for free: `confined` (head loops inside one block
  window) and `runaway` (pass-through of blank block into the same state).
- `bin/run.mjs` — CLI: `node bin/run.mjs <machine> [--k N] [--ops N]
  [--naive maxSteps] [--sample N]`. `--sample` records compressed configs,
  groups them by shape signature, prints per-run count progressions — the
  raw material for guessing induction rules.
- `tools/validate.mjs` — exact-step regression against BB(2)–BB(5) champions
  (BB(5) = 47,176,870 steps) across k=1..4. Run before trusting any change.
- `tools/triage.mjs` — sweeps `data/open.txt` at k=1..4, ranks by steps
  reached per macro-op. High compression ⇒ regular counter/bouncer behavior
  ⇒ best candidates for hand-provable induction rules.

## Odometer-specific tools

- `tools/ledger.mjs` — enumerates the true orbit base→death (549 events,
  exact BigInt sweep totals; `CHECK_SWEEPS` cross-checks against plain
  iteration). `tools/genledger.mjs` generates `coq/OdometerLedger.v`
  from its output.
- `tools/clock.mjs` / `tools/toyclock.mjs` — derive + validate the exact
  per-sweep step-cost law. `tools/nhalt.mjs` — exact N_halt
  (modes `toy6|toy9|real`; toys reproduce raw halting steps exactly).
- `tools/census.mjs`, `tools/dipwalk.mjs`, `tools/rawrules.mjs`,
  `tools/rungcheck.mjs` — block-transition census, anchor validation,
  raw-level testbenches.

Step counting is BigInt end to end; the S(n) convention counts the halting
transition as a step. All simulation is exact — no sampling or approximation
in the step counts.
