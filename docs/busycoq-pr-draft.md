# DRAFT: PR to ccz181078/busycoq (BB6 branch)

**NOT POSTED.** For Jacob's approval first.

- from: `JacobRSchwartz-AI/busycoq:mirror-ubrrba-halt` (not yet pushed)
- into: `ccz181078/busycoq:BB6`
- base commit: `7583181`, one commit on top: `6eb07e1`
- files: `verify/UBRRBAHaltFlipv1.v` (new), `verify/Inductive_inf.v` (one CLI mode added)

---

## Title

`UBRRBAHaltFlipv1: decide mirror-orientation holdouts with the UBRRBA decider`

## Body

The UBRRBA decider needs the counter's most significant digit on the right
of the tape. A holdout listed in the opposite orientation is therefore
invisible to it as listed, even when its mirror image decides fine. This
adds the reorientation as a function on machines so those holdouts can be
proved directly, without rewriting transition strings by hand.

`verify/UBRRBAHaltFlipv1.v` defines `mirror : TM -> TM` and proves
`mirror_halts_at_trans`, which transfers the decider's certificate back to
the machine in its listed orientation. The user-facing piece is one tactic:

    solve_halt_mirror bsz

which is `solve_halt bsz` for a machine whose mirror is the decidable one.

### Why the mirror lemmas are restated here

`Individual62`'s `Flip` module is a separate application of the TM functor,
and its step family is not kernel-convertible with `Inductive62`'s. So
`Flip.flip_halts_iff` cannot be applied to a goal stated over
`Inductive62.halts_at_trans`. The lemmas here are the same argument
restated against `Inductive62`'s own `step`, which is what the decider
certificates live in. If you would rather this reuse `Flip` through an
explicit bridge, I am happy to redo it that way.

### What it decides

    Lemma tmf1 : halts_at_trans
      (TM_from_str "1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA") c0 (D, 0).
    Proof. solve_halt_mirror 12. Qed.

This machine is the reason the gap was noticed. It was already provable in
this repo, but only as its hand-mirrored string
(`UBRRBAHaltv2.tm105`). With this it is provable as listed.

### Scope, stated plainly

I ran all 598 remaining BB6 holdouts through the mirrored decider at the
same budget (block sizes as in the existing UBRRBA usage, `maxT = 200000`).
**Zero further hits.**

So this PR recovers exactly one machine, and that machine already had a
proof under a different string. What it actually buys is that the
orientation gap is closed as a capability: any future holdout whose mirror
is UBRRBA-decidable now gets a one-line proof, and nobody has to notice by
hand that a mirror is needed. If you would rather have the capability
without the single certificate, or the certificate folded into
`UBRRBAHaltv2` instead of a new file, say which and I will restructure.

### The Inductive_inf.v change

One case added to the CLI dispatcher, `UBRRBAT`, which runs
`ubrrba_upds` on a machine string at a given block size and budget. I used
it to drive the 598-machine sweep above. It is independent of the proof
material and I am glad to drop it or split it into its own PR if you prefer
to keep that file untouched.

### Build

Compiles against the current `BB6` head. `tmf1` uses `native_cast_no_check`
through the existing `solve_halt` machinery, so `Print Assumptions` shows
the same primitives the other UBRRBA certificates rely on and nothing
further.

---

Jacob Schwartz & Claude Fable 5, joint work.
