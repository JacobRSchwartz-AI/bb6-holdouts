# bb6-holdouts

**TL;DR: We found that a famous open problem's list of "undecided"
machines contains one that actually halts — and we proved it with a
computer-checked proof.**

## Background, in plain terms

A Turing machine is the simplest possible model of a computer: a tape of
0s and 1s, a head that reads one cell at a time, and a small table of
rules. The **Busy Beaver problem** asks: among all Turing machines with
*n* rules ("states"), which one runs the longest before stopping?
Machines that never stop don't count — so to answer it you must sort
every machine into "halts" or "runs forever," which is famously
undecidable in general.

The [bbchallenge](https://bbchallenge.org) community settled n = 5 in
2024 (the champion runs 47,176,870 steps). For **n = 6** they maintain a
list of **holdouts**: machines that automated deciders couldn't
classify, each needing individual human analysis. This repo contains
tooling for attacking those holdouts — and one fully solved case.

## The result

The holdout machine `1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA`
(that string is its complete rule table; we nicknamed it **the
Odometer** because its tape behaves like a mileage counter that ticks,
carries, and rolls over) **halts**. We also computed a conjectured
exact step count:

    N_halt = 67931323646787744340347982457788840036504581967495927710
             77171340442123492305867933761244645774908114601585353157
             21018132084275421883147320661638136374334659122557882929
             34

That's a 170-digit number, about 6.8 × 10^169 — you could never
run the machine to see this; the universe's ~10^80 atoms working since
the Big Bang wouldn't scratch it. The only way to know is to *prove* it.

Two independent artifacts back the claim:

1. **A machine-checked proof that it halts.** `coq/OdometerLedger.v`
   ends in `Theorem odometer_halts : halts tm c0` — checked by
   [Coq](https://coq.inria.fr/), a proof assistant whose kernel accepts
   nothing but airtight logic, building on the community's
   [busycoq](https://github.com/meithecatte/busycoq) framework.
   `Print Assumptions` confirms the proof uses **zero axioms**: every
   step reduces to Coq's core logic. A GitHub Actions workflow
   ([.github/workflows/coq-verify.yml](.github/workflows/coq-verify.yml))
   rebuilds the whole proof from a fresh busycoq clone on every push.
2. **The conjectured step count.** The proof certifies *that* it halts; the
   170-digit *count* comes from an exact per-step cost formula
   (`tools/nhalt.mjs`), derived from instrumented runs (residual zero
   over 3000 measured sweeps) and validated by reproducing — to the
   exact step — the halting times of two miniature odometers small
   enough to run raw (154,134 and 33,925,642 steps).

Why it was a holdout: the machine spends almost its whole life in an
extremely regular counting loop — it *looks* immortal, and an earlier
informal analysis (ours included) argued it runs forever. Formalizing
that argument in Coq is what exposed the flaw: the counter's carry rule
breaks exactly once per "era," at a boundary no simulation had ever
reached, and after 549 such events the machine crashes into its own
scaffolding and halts. The full discovery story, evidence chain, and
submission plan are in [docs/submission.md](docs/submission.md);
day-by-day working notes in [notes/odometer.md](notes/odometer.md).

**Authors:** Jacob Schwartz & Claude Fable 5, joint work.

## Reproducing the proof

Requires Coq 8.18. The full chain compiles in a few minutes with peak
memory under 1GB — any laptop works. (An earlier version of
`OdometerOrbit.v` demanded >32GB until two monolithic reductions were
restated as small-step lemmas; the git history tells that story.)
This is exactly what CI runs:

```sh
git clone https://github.com/meithecatte/busycoq
cp coq/*.v busycoq/verify/
cd busycoq/verify
coq_makefile -Q . BusyCoq -o Makefile.port \
  LibTactics.v Helper.v Pigeonhole.v TM.v Compute.v Flip.v Permute.v \
  Individual.v BB62.v Individual62.v Odometer.v OdometerDip.v \
  OdometerOrbit.v OdometerCrisis.v OdometerBase.v OdometerLedger.v
make -f Makefile.port -j1
echo 'Require Import BusyCoq.OdometerLedger. Print Assumptions odometer_halts.' > check.v
coqtop -Q . BusyCoq -batch -l check.v
```

Success looks like: `make` finishes with no errors, and the last command
prints `Closed under the global context` — Coq's way of saying "proved,
no assumptions."

To check the step count: `node tools/nhalt.mjs toy6`, `toy9` (each
prints the exact known answer), then `node tools/nhalt.mjs real`.

## What's in the repo

| Path | What it is |
|---|---|
| `coq/` | The proof. `Odometer*.v` are ours; they build on busycoq. |
| `viz/index.html` | Interactive visualization — open it in a browser and press play to watch the machine's whole life, genesis to halt. Self-contained; every frame is the exact tape, recomputed live (the page re-derives the 549-event ledger and cross-checks raw simulation against the abstract dip machine on load). |
| `tools/ledger.mjs` | Enumerates the machine's true orbit from its proven starting anchor to its death — 549 carry-overflow events — with exact BigInt totals. `genledger.mjs` turns that into `OdometerLedger.v`. |
| `tools/clock.mjs`, `toyclock.mjs`, `nhalt.mjs` | Derive, validate, and apply the exact step-cost formula → N_halt. |
| `tools/census.mjs`, `dipwalk.mjs`, `rawrules.mjs`, `rungcheck.mjs` | Ground-truth testbenches: verify the abstract model against millions of raw machine steps. |
| `notes/odometer.md` | The lab notebook: every prediction registered before its test, graded honestly after — including the failures that redirected the work. |
| `docs/submission.md` | The claim, evidence table, and submission checklist. |
| `src/`, `bin/`, `data/` | General holdout-hunting toolkit (below). |

## General toolkit (any holdout)

Node ≥22, no dependencies. `src/macro.mjs` is the workhorse simulator:
k-cell macro blocks over a run-length-encoded tape with shift-rule
acceleration, exact BigInt step counting throughout. `bin/run.mjs` is
the CLI; `tools/validate.mjs` regression-tests it against the known
BB(2)–BB(5) champions; `tools/triage.mjs` ranks the open holdout list
(`data/open.txt`, from the community tracker snapshot
`data/holdouts-1534.csv`) by how well each machine compresses — a proxy
for "regular enough to prove things about."
