# Final Discourse post text. Approved edits: attribution simplified,
# step count marked conjectural, no em dashes.

**Category:** Individual machines
**Title:** BB(6) holdout `1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA` ("the Odometer") halts: machine-checked Coq certificate

---

We are reporting that the BB(6) holdout

    1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA

halts. The claim comes with a machine-checked Coq certificate
(busycoq, Coq 8.18, zero axioms), a clean-clone CI run, and a
one-command reproduction script. We believe the machine should move
to the halting column.

Repo: https://github.com/JacobRSchwartz-AI/bb6-holdouts

**Why it held out.** The machine is an odometer. Its tape spells a
base-16 counter, three 4-bit blocks per digit, and one sweep adds
exactly 1, carries included. In any simulation it looks immortal, and
an informal non-halt argument (ours) survived 100M-step censuses and
seeded validations at scales up to 2^283. The catch: the counter
grows by consuming a finite reservoir of boundary blocks. Three
blocks buy one new digit, the reservoir funds exactly 71 digits, and
the first carry after it runs dry walks into the machine's one
undefined transition (state D reading 0). The fatal sweep is
tail-clock sweep 3 * 2^279 exactly.

**The certificate.** `Theorem odometer_halts : halts tm c0` in
`coq/OdometerLedger.v`; `Print Assumptions` reports "Closed under the
global context". Structure:

- A block-level abstract machine over 4-bit glyphs ("the dip"),
  proved equivalent to the raw TM, one lemma per block rule, with the
  rule set sealed by a census over 100M raw steps.
- An increment theorem: below group capacity, one dip adds exactly 1
  to the spelled counter, parametrically. This covers the long quiet
  spans in one lemma.
- A generated ledger: from a kernel-computed base anchor (step
  354,540), the real orbit is an alternation of parametric spans and
  549 concrete carry-overflow events, each re-checked by vm_compute.
  The composed chain ends at the dying string, and a dying dip is
  proved to reach the undefined transition.

**Reproduction.** Clean busycoq clone, copy in the `.v` files, make.
The chain compiles in a few minutes with peak memory under 1GB, so
any laptop works. CI reruns the full verification, including the
axiom check, on every push.

**Conjectured step count.** We also computed an exact halting step
count:

    N_halt = 67931323646787744340347982457788840036504581967495927710
             77171340442123492305867933761244645774908114601585353157
             21018132084275421883147320661638136374334659122557882929
             34

(170 digits, about 6.79 * 10^169). It comes from a per-sweep clock
law with residual zero over 3,000 instrumented sweeps, summed in
closed form over the orbit; the identical pipeline reproduces the raw
halting times of two miniature odometers of the same structure
exactly (154,134 and 33,925,642 steps). We present this as a
validated conjecture: the Coq theorem certifies halting only. A
counted-relation port that certifies the number is planned as a
follow-up.

**How the error was caught.** The non-halt argument died during
formalization: a ten-line closure test showed the increment law fails
at exactly one value per era, at a boundary no simulation had ever
crossed. A second plausible mechanism (a "crisis ladder") was proved
mechanically correct in Coq and then shown unreachable by end-to-end
enumeration of the actual orbit. The rule we took away, and would
offer to anyone doing seeded validation: every seeded validation
needs a reachability argument for its seed. The repo includes the lab
notebook with the full prediction register, failures included.

Two questions for the community: where should a halting certificate
best live long-term (busycoq is non-halt focused; happy to PR
wherever is preferred), and is there prior art on exact step counts
at this scale?

Jacob Schwartz & Claude Fable 5, joint work.
