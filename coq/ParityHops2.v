From BusyCoq Require Import Individual62.
From BusyCoq Require Import Parity.
From BusyCoq Require Import ParityHops.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
Set Default Goal Selector "!".

(** Mechanism-level lemmas for the two composed-hop shapes flagged by the
    tracing pass (notes/parity.md, digit-birth mechanism): C:shift1's
    odd-run gap-2 partial exit (Target A) and digitBirth2's four-level
    capped-carry consumption (Target B). Every equation below was
    validated by hand-simulating exc's Fixpoint AND fuzz-checked (700+
    random trials, 0 mismatches) against a literal transcription of exc
    before being encoded here; scratchpad verify-formulas.mjs. Both
    targets turn out to be pure ALGEBRA over the existing exc_insulate /
    exc_run_t / exc_zz toolkit plus one small generalization
    (exc_absorb_gen), not a fresh fuel induction -- see the task report
    for why. *)

(** ** exc_absorb generalized to an arbitrary rs-tail.

    exc_absorb (Parity.v) hardcodes rs = cons x nil because that is the
    shape at its own call site (mstep's right-edge branch). The
    machinery underneath (exc_odd_t) is already polymorphic in rs; this
    is the same proof with `nil` widened to `rest`, needed because
    Target A's odd run is reached AFTER a gap-2 cs step has already
    grown rs to more than one entry. *)
Lemma exc_absorb_gen : forall j x rest wt,
  exc ([1]^^(2 * j + 1) ++ cons 0 wt) false (cons x rest)
  = ExB (cons 1 wt) (prep j (cons (S x) rest)).
Proof.
  destruct j; introv.
  - reflexivity.
  - replace (2 * S j + 1) with (S (S (2 * j + 1))) by lia.
    cbn [lpow]. rewrite <- List.app_assoc. cbn [List.app].
    change (exc (cons 1 (cons 1 ([1]^^(2 * j + 1) ++ cons 0 wt))) false (cons x rest))
      with (exc ([1]^^(2 * j + 1) ++ cons 0 wt) true (cons (S x) rest)).
    rewrite exc_odd_t. reflexivity.
Qed.

Lemma exc_absorb_nil_gen : forall j x rest,
  exc ([1]^^(2 * j + 1)) false (cons x rest)
  = ExB (cons 1 nil) (prep j (cons (S x) rest)).
Proof.
  destruct j; introv.
  - reflexivity.
  - replace (2 * S j + 1) with (S (S (2 * j + 1))) by lia.
    cbn [lpow].
    change (exc ([1] ++ [1] ++ [1]^^(2 * j + 1)) false (cons x rest))
      with (exc ([1]^^(2 * j + 1)) true (cons (S x) rest)).
    rewrite exc_odd_t_nil. reflexivity.
Qed.

Print Assumptions exc_absorb_gen.
Print Assumptions exc_absorb_nil_gen.

(** ** TARGET A: the odd-run gap-2 partial-run exit.

    Dispatch shape MC ([1]^(2j+5) ++ [0;0] ++ [1]^(2i+1) ++ 0::wt) [L]:
    the run feeding the excursion is odd (2j+5, mstep's own peel leaves
    2j+4, an exc_insulate shape), the gap immediately below it is
    exactly 2 (too short for an uncapped excursion to exit on, but
    exactly what a CAPPED excursion tunnels through via push3), and what
    lies past the gap is itself an odd run (2i+1) that gets walked
    carry-by-carry until its own odd leftover cell meets a 0-boundary
    and exits B-side, mid-run. Reproduced live: harness on
    {top:2, stack:[[3,2]], H:5, W:[], p:6, L:4} (the 34-step C:shift1
    instance), where this fires at mstep call #26 (after the second
    absorb+skim): j=2, i=1, wt=[0;0;1;1], L=16, landing
    B ws=[1;0;0;1;1] rs=[1;5;1;1;20] -- matches this lemma exactly. *)
Lemma mstep_gap2_run_odd : forall j i wt L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+5) ++ [0;0] ++ [1]^^(2*i+1) ++ cons 0 wt) (cons L nil)) =
  Some (MB (cons 1 wt) (prep i (cons 5 (prep j (cons (4 + L) nil))))).
Proof.
  introv HL.
  replace (([1]^^(2*j+5) ++ [0;0] ++ [1]^^(2*i+1) ++ cons 0 wt)%list)
    with ((cons 1 ([1]^^(2*j+4) ++ [0;0] ++ [1]^^(2*i+1) ++ cons 0 wt))%list)
    by (replace (2*j+5) with (S (2*j+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_insulate j (3 + L) ([0;0] ++ [1]^^(2*i+1) ++ cons 0 wt)%list).
  rewrite (exc_run_t j).
  rewrite prep_comm.
  cbn [exc push3 cpush List.app].
  rewrite exc_absorb_gen.
  reflexivity.
Qed.

(** Same mechanism when the odd run is the last thing on the wall (the
    trailing 0::wt is absent): exc_absorb_nil_gen in place of
    exc_absorb_gen. *)
Lemma mstep_gap2_run_odd_nil : forall j i L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+5) ++ [0;0] ++ [1]^^(2*i+1)) (cons L nil)) =
  Some (MB (cons 1 nil) (prep i (cons 5 (prep j (cons (4 + L) nil))))).
Proof.
  introv HL.
  replace (([1]^^(2*j+5) ++ [0;0] ++ [1]^^(2*i+1))%list)
    with ((cons 1 ([1]^^(2*j+4) ++ [0;0] ++ [1]^^(2*i+1)))%list)
    by (replace (2*j+5) with (S (2*j+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_insulate j (3 + L) ([0;0] ++ [1]^^(2*i+1))%list).
  rewrite (exc_run_t j).
  rewrite prep_comm.
  cbn [exc push3 cpush List.app].
  rewrite exc_absorb_nil_gen.
  reflexivity.
Qed.

Print Assumptions mstep_gap2_run_odd.
Print Assumptions mstep_gap2_run_odd_nil.

(** ** TARGET B: the four-level capped-carry consumption.

    After H's own bury+lapA cycle the excursion re-enters a wall shaped
    [1]^(2j+5) ++ [0;0] ++ [1;1] ++ [0;0] ++ [1]^(2i+4) ++ deeper: H's
    own leftover gap-2, F.top=2's buried run (always exactly a 2-run --
    mstep_bury only ever manufactures a fresh top-2), the contacted
    stack entry's own gap-2, and its run (even, >=4, the digit-9
    accumulator). All four levels resolve in ONE mstep call: two more
    capped gap-2 tunnels (exc_zz-shaped, cap flips true then true then
    false across the fixed six cells) plus one more carry-pair peeled
    off the run before the general remainder falls to exc_run_t.
    Reproduced live (harness, small-p synthetic instances of
    digitBirth2:term): {top:2,stack:[[2,4]],H:4,W:[],p:2,L:10} (run=4,
    i=0) landing rs=[4,9,18] at mstep call #7, and
    {top:2,stack:[[2,6]],H:4,W:[],p:2,L:10} (run=6, i=1) landing
    rs=[4,1,9,18] -- both instances of the JSON digitBirth2:term rule
    (W' = [1 x (run-4)/2, 9]); the full orbit examples (p=24/p=8/p=86)
    replay the same mechanism, only the leading pump count differs. *)
Lemma exc_gap2x2_run_even : forall j i deeper x,
  exc ([1]^^(2*j+4) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ deeper) false (cons x nil) =
  exc deeper true (prep (S i) (cons 9 (prep j (cons (S x) nil)))).
Proof.
  introv.
  rewrite (exc_insulate j x ([0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ deeper)%list).
  rewrite (exc_run_t j).
  rewrite prep_comm.
  cbn [exc push3 cpush List.app].
  replace (2*i+4) with (2 + 2 * (S i)) by lia.
  rewrite lpow_app_assoc.
  cbn [exc cpush List.app lpow].
  rewrite (exc_run_t (S i)).
  reflexivity.
Qed.

Print Assumptions exc_gap2x2_run_even.

(** mstep-level closure for the case the run is the last thing on the
    wall (digitBirth2:term): deeper = nil resolves exc's own nil clause,
    landing on the fresh top-2 base state. *)
Lemma mstep_gap2x2_run_even_nil : forall j i L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+5) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4)) (cons L nil)) =
  Some (MC (cons 1 (cons 1 nil))
           (cons 4 (prep i (cons 9 (prep j (cons (4 + L) nil)))))).
Proof.
  introv HL.
  replace (([1]^^(2*j+5) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4))%list)
    with ((cons 1 ([1]^^(2*j+4) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ nil))%list)
    by (replace (2*j+5) with (S (2*j+4)) by lia;
        rewrite List.app_nil_r; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_gap2x2_run_even j i nil (3 + L)).
  cbn [exc of_exit push3 prep List.app].
  reflexivity.
Qed.

Print Assumptions mstep_gap2x2_run_even_nil.
