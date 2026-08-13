# bb6-holdouts

Hunting non-halting proofs for open BB(6) holdout machines
(https://wiki.bbchallenge.org/wiki/BB(6)). Node ≥22, no dependencies.

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

Step counting is BigInt end to end; the S(n) convention counts the halting
transition as a step. All simulation is exact — no sampling or approximation
in the step counts.

Proof targets: characterize a machine's configs as a closed family, show the
family is closed under the transition relation and contains no halting
config. Submission path: bbchallenge forum/wiki, ideally later formalized
against busycoq (https://github.com/ccz181078/busycoq).
