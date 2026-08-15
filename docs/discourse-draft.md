# DRAFT Discourse post — reviewed by Jacob before posting. Not public.

**Proposed category:** Individual machines
**Proposed title:** BB(6) holdout `1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA` halts (Coq certificate, exact step count)

---

We'd like to report that the BB(6) holdout

    1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA

("the Odometer" — its tape behaves like a base-16 counter that mints
new digits by consuming a finite reservoir) **halts**, with a
machine-checked Coq certificate, and we believe it should move to the
halting column.

**The certificate.** `Theorem odometer_halts : halts tm c0`, built on
busycoq (Coq 8.18). `Print Assumptions` reports *Closed under the
global context* — zero axioms. The pipeline:

- a block-level abstract machine ("the dip") over 4-bit glyphs, proved
  equivalent to the raw TM (one lemma per census-sealed block rule);
- an increment theorem: one sweep adds exactly 1 to the counter the
  tape spells, parametrically below group capacity — this covers the
  quiet spans;
- a generated ledger: the real orbit from a kernel-computed base
  anchor (step 354,540) to death is an alternation of parametric spans
  and 549 concrete carry-overflow events, each re-checked by
  vm_compute; composing them reaches the dying string, whose dip has
  no successor — which in the raw machine is state D reading 0, the
  undefined transition.

The full chain compiles from a clean busycoq clone in a few minutes,
peak memory under 1GB; the repo has a one-command reproduction script
and a CI workflow that reruns the whole verification (including the
axiom check) on every push.

**The exact step count.** The halting step, computed exactly:

    N_halt = 67931323646787744340347982457788840036504581967495927710
             77171340442123492305867933761244645774908114601585353157
             21018132084275421883147320661638136374334659122557882929
             34

(170 digits, ≈ 2^564.17 ≈ 6.79·10^169; the fatal sweep is tail-clock
sweep 3·2^279 exactly). Honesty note: the Coq theorem certifies *that*
the machine halts; N_halt itself is a separate exact computation — a
per-sweep clock law with residual zero over 3,000 instrumented sweeps,
summed in closed form over the orbit — validated by reproducing the
raw halting times of two miniature odometers of the same structure
(154,134 and 33,925,642 steps) exactly. A counted-relation Coq port
that certifies the number itself is planned as a follow-up.

**How it was found (and almost wasn't).** An informal non-halt
argument for this machine survived 100M-step censuses and seeded
validations at scales up to 2^283 — and was wrong. The flaw was found
while formalizing: a ten-line closure test showed dip(spell v) =
spell(v+1) fails at exactly one value per era, at a boundary no
simulation had crossed. The same lesson then struck again: a
mechanically flawless "crisis ladder" was proved in Coq and turned out
unreachable by the real orbit. The cure that stuck: enumerate the
actual orbit end to end from the proven base anchor, with every
acceleration step mirroring a proved lemma and every event re-checked
by vm_compute. We'd summarize the transferable lesson as: *every
seeded validation needs a reachability argument for its seed.*

**Repo:** [link — currently private; will be public at posting time]
— proof sources, the enumeration/validation toolchain, reproduction
script, CI, and a lab notebook with the full prediction-register
history, including the failed predictions.

Questions we'd appreciate the community's view on: where a *halting*
certificate best lives long-term (busycoq is non-halt-focused — happy
to PR wherever is preferred), and any prior art on exact step counts
at this scale.

— Jacob Schwartz & Claude (Anthropic), joint work
(direction, prediction-first protocol, and the empirical campaign:
Jacob; formalization and tooling: Claude, under Jacob's direction)
