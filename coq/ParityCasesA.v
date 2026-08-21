From BusyCoq Require Import Individual62.
From BusyCoq Require Import Parity.
From BusyCoq Require Import ParityHops.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
Set Default Goal Selector "!".

(** Composed hop lemmas for the validated architecture-A chunkstep cases
    (notes/parity.md, "The chunkstep successor map"; tools/chunkstep-cases.json
    keys chunkBig, A:cleanK0/A:chunkCascade/A:chunkTerm, A:g3, A:g3term).
    Every lemma's instance and step count was replayed against a literal JS
    transcription of Coq's own mstep before being encoded here (see the task
    report for the exact instances). *)

(** ** Target 1: chunkBig generalized.

    chunkBig (Parity.v) fixes the wall below the buried head at
    `stackw gs` (source top 2, pushed run 2) and H at 4c+8. The bury +
    absorb + insulate skeleton (mstep_bury, lapA, lapI_exit) never
    inspects what is glued on past the leading two 1s it manufactures, so
    the wall argument generalizes to an arbitrary list, with the proof
    otherwise unchanged: chunkBig_w. Instantiating that argument at
    `[1;1;1;1]++wt` (an explicit 4-run) gives the "source top 4" case
    (chunkBig_w4); g := 3 gives H = 9 (chunkBig9 / chunkBig9_4). All four
    are corollaries of the one lemma. *)

Lemma chunkBig_w : forall (W : list Sym) (g p L : nat),
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC W (cons (g + 6) (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ W))) (cons 4 (prep p (cons (8 + L) nil)))).
Proof.
  introv HL.
  cbn [mrun].
  replace (g + 6) with (S (S (S (S (g + 2))))) by lia.
  rewrite mstep_bury by apply prep_ne.
  rewrite mrun_app.
  replace (([0]^^(S (S (S (g + 2)))) ++ W)%list)
    with ((cons 0 ([0]^^(S (S (g + 2))) ++ W))%list)
    by reflexivity.
  rewrite (lapA (S p) _ L HL).
  replace (([0]^^(S (S (g + 2))) ++ W)%list)
    with (([0]^^(4 + g) ++ W)%list)
    by (do 2 f_equal; lia).
  rewrite lapI_exit
    by (replace (S (3 + L)) with (S (S (S (S L)))) by lia;
        cbn [Nat.even]; assumption).
  reflexivity.
Qed.

Corollary chunkBig_w4 : forall (wt : list Sym) (g p L : nat),
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 (cons 1 (cons 1 wt))))
        (cons (g + 6) (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ cons 1 (cons 1 (cons 1 (cons 1 wt))))))
           (cons 4 (prep p (cons (8 + L) nil)))).
Proof. introv HL. exact (chunkBig_w (cons 1 (cons 1 (cons 1 (cons 1 wt)))) g p L HL). Qed.

Corollary chunkBig9 : forall (W : list Sym) (p L : nat),
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC W (cons 9 (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 ([0; 0; 0] ++ W))) (cons 4 (prep p (cons (8 + L) nil)))).
Proof. introv HL. exact (chunkBig_w W 3 p L HL). Qed.

Corollary chunkBig9_4 : forall (wt : list Sym) (p L : nat),
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 (cons 1 (cons 1 wt)))) (cons 9 (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 ([0; 0; 0] ++ cons 1 (cons 1 (cons 1 (cons 1 wt))))))
           (cons 4 (prep p (cons (8 + L) nil)))).
Proof. introv HL. exact (chunkBig_w4 wt 3 p L HL). Qed.

(** ** Target 2: chunkCascade/chunkTerm generalized.

    chunkCascade (Parity.v) fixes the contact entry's gap at 4c+6 (the
    stackw encoding also fixes its run at 2); mstep_insulate_carryexit
    already takes an arbitrary `[0]^^(4+g) ++ tail` for that entry, so the
    generalization to ANY gap >= 4 (any residue, not just 6 mod 4) and an
    arbitrary run/deeper-stack tail is a direct restatement plugging that
    lemma (via lapI_cascade) into the same bury + absorb skeleton
    chunkCascade itself uses -- no new machinery, exactly as flagged.
    chunkTerm's blank-terminal case needs no change: its own conclusion is
    already `cons 1 (cons 1 nil)`, i.e. top' = 2 (settling the "top' = 4?"
    question from the task brief -- see the report). *)

Lemma chunkCascade_w : forall (k g p L : nat) (tail : list Sym),
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 (blocks k ([0]^^(4 + g) ++ tail))))
        (cons 4 (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ tail)))
           (cons (4 * k + 8) (prep p (cons (8 + L) nil)))).
Proof.
  introv HL.
  cbn [mrun].
  change 4 with (S (S (S (S 0)))).
  rewrite mstep_bury by apply prep_ne.
  rewrite mrun_app.
  replace (([0]^^(S (S (S 0))) ++ cons 1 (cons 1 (blocks k ([0]^^(4 + g) ++ tail))))%list)
    with ((cons 0 (cons 0 (cons 0 (cons 1 (cons 1 (blocks k ([0]^^(4 + g) ++ tail)))))))%list)
    by reflexivity.
  rewrite (lapA (S p) _ L HL).
  change (cons 0 (cons 0 (cons 1 (cons 1 (blocks k ([0]^^(4 + g) ++ tail))))))
    with (blocks (S k) ([0]^^(4 + g) ++ tail)).
  rewrite lapI_cascade
    by (replace (S (3 + L)) with (S (S (S (S L)))) by lia;
        cbn [Nat.even]; assumption).
  cbn [mrun prep].
  rewrite iter4_head.
  cbn [push3].
  do 4 f_equal; lia.
Qed.

(** ** Targets 3-4: the A:g3 double lap and A:g3term.

    A gap-3 contact (H = 4, top = 2, after k leading (2,2) stack entries)
    is not resolved by mstep_insulate_gap3 (ParityHops.v) directly: that
    lemma needs the run of 1s to abut a zero immediately, but here the
    excursion first re-crosses the wall's OWN top-2 block and three more
    zeros before it ever reaches the contact's run -- a nesting
    mstep_insulate_gap3 does not cover on its own, so mstep_insulate_g3nest
    below reproves the same exc_insulate/exc_run_t/exc_blocks skeleton one
    layer deeper. Composed with a bury+absorb round (lapA) it gives
    chunkA_g3_short: H = 4 buries, the k-chain and the gap-3 entry all
    resolve in one non-terminal excursion, landing on a FRESH H = 4k+8
    with the contact's run bumped by one and glued straight to the deeper
    tail (no gap in between). That landing is already a valid boundary
    when the bumped run is exactly 4 (i.e. the source run was 3) with
    nothing else needed -- chunkA_g3term. Otherwise a second full
    chunkBig_w round re-buries it: chunkA_g3, the double lap (two p-laps,
    p -= 4, L += 16). *)

Lemma mstep_insulate_g3nest : forall j k rest2 L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2 * j + 5) ++ blocks k ([0; 0; 1; 1; 0; 0; 0] ++ cons 1 rest2))
            (cons L nil)) =
  Some (MC (cons 1 (cons 1 rest2)) (cons (4 * k + 8) (prep j (cons (4 + L) nil)))).
Proof.
  introv HL.
  replace (([1]^^(2 * j + 5) ++ blocks k ([0; 0; 1; 1; 0; 0; 0] ++ cons 1 rest2))%list)
    with ((cons 1 ([1]^^(2 * j + 4) ++ blocks k ([0; 0; 1; 1; 0; 0; 0] ++ cons 1 rest2)))%list)
    by (replace (2 * j + 5) with (S (2 * j + 4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_insulate j (3 + L) (blocks k ([0; 0; 1; 1; 0; 0; 0] ++ cons 1 rest2))).
  rewrite (exc_run_t j).
  rewrite prep_comm.
  change (cons (S O) (prep j (cons (S (3 + L)) nil)))
    with (prep (S j) (cons (S (3 + L)) nil)).
  rewrite exc_blocks.
  cbn [prep].
  rewrite iter4_head.
  replace (([0; 0; 1; 1; 0; 0; 0] ++ cons 1 rest2)%list)
    with (cons 0 (cons 0 (cons 1 (cons 1 (cons 0 (cons 0 (cons 0 (cons 1 rest2))))))))
    by reflexivity.
  cbn [exc of_exit push3 cpush].
  f_equal. f_equal. f_equal. lia.
Qed.

Lemma lapG3nest : forall n k rest2 L,
  Nat.even L = true ->
  mrun (S n + 1)
    (MC (cons 1 (cons 1 (cons 1 (blocks k ([0; 0; 1; 1; 0; 0; 0] ++ cons 1 rest2)))))
        (prep (S n) (cons L nil))) =
  Some (MC (cons 1 (cons 1 rest2)) (cons (4 * k + 8) (prep n (cons (4 + L) nil)))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite mrun_pump.
  rewrite wpump_lpow.
  cbn [mrun].
  replace (([1]^^(2 * S n)
            ++ cons 1 (cons 1 (cons 1 (blocks k ([0; 0; 1; 1; 0; 0; 0] ++ cons 1 rest2)))))%list)
    with (([1]^^(2 * n + 5) ++ blocks k ([0; 0; 1; 1; 0; 0; 0] ++ cons 1 rest2))%list)
    by (replace (2 * n + 5) with (2 * S n + 3) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_insulate_g3nest n k rest2 L HL).
  reflexivity.
Qed.

Lemma blocks_swap : forall k (X : list Sym),
  blocks (S k) X = blocks k ([0; 0; 1; 1] ++ X).
Proof.
  induction k; introv.
  - reflexivity.
  - change (blocks (S (S k)) X) with ((0 :: 0 :: 1 :: 1 :: blocks (S k) X)%list).
    rewrite IHk. reflexivity.
Qed.

Lemma chunkA_g3_short : forall k r tail p L,
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 (blocks k ([0; 0; 0] ++ [1]^^(S r) ++ tail))))
        (cons 4 (prep (S (S p)) (cons L nil)))) =
  Some (MC ([1]^^(S (S r)) ++ tail) (cons (4 * k + 8) (prep p (cons (8 + L) nil)))).
Proof.
  introv HL.
  cbn [mrun].
  change 4 with (S (S (S (S 0)))).
  rewrite mstep_bury by apply prep_ne.
  rewrite mrun_app.
  replace (([0]^^(S (S (S 0)))
            ++ cons 1 (cons 1 (blocks k ([0; 0; 0] ++ [1]^^(S r) ++ tail))))%list)
    with ((cons 0 (cons 0 (cons 0
            (cons 1 (cons 1 (blocks k ([0; 0; 0] ++ [1]^^(S r) ++ tail)))))))%list)
    by reflexivity.
  rewrite (lapA (S p) _ L HL).
  change (cons 0 (cons 0 (cons 1 (cons 1 (blocks k ([0; 0; 0] ++ [1]^^(S r) ++ tail))))))
    with (blocks (S k) ([0; 0; 0] ++ [1]^^(S r) ++ tail)).
  rewrite blocks_swap.
  change ([0; 0; 1; 1] ++ ([0; 0; 0] ++ [1]^^(S r) ++ tail))%list
    with ([0; 0; 1; 1; 0; 0; 0] ++ cons 1 ([1]^^r ++ tail))%list.
  rewrite lapG3nest
    by (replace (S (3 + L)) with (S (S (S (S L)))) by lia;
        cbn [Nat.even]; assumption).
  reflexivity.
Qed.

Lemma chunkA_g3term : forall k tail p L,
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 (blocks k ([0; 0; 0] ++ [1]^^3 ++ tail))))
        (cons 4 (prep (S (S p)) (cons L nil)))) =
  Some (MC ([1]^^4 ++ tail) (cons (4 * k + 8) (prep p (cons (8 + L) nil)))).
Proof. introv HL. exact (chunkA_g3_short k 2 tail p L HL). Qed.

Lemma chunkA_g3 : forall k r tail p L,
  Nat.even L = true ->
  mrun (S ((S (S (S (S p))) + 2) + (S (S (S p)) + 1))
        + S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 (blocks k ([0; 0; 0] ++ [1]^^(S r) ++ tail))))
        (cons 4 (prep (S (S (S (S p)))) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 ([0]^^(4 * k + 2) ++ [1]^^(S (S r)) ++ tail)))
           (cons 4 (prep p (cons (16 + L) nil)))).
Proof.
  introv HL.
  assert (HL8 : Nat.even (8 + L) = true).
  { replace (8 + L) with (S (S (S (S (S (S (S (S L)))))))) by lia.
    cbn [Nat.even]. exact HL. }
  rewrite mrun_app.
  rewrite (chunkA_g3_short k r tail (S (S p)) L HL).
  replace (4 * k + 8) with (4 * k + 2 + 6) by lia.
  rewrite (chunkBig_w ([1]^^(S (S r)) ++ tail) (4 * k + 2) p (8 + L) HL8).
  replace (8 + (8 + L)) with (16 + L) by lia.
  reflexivity.
Qed.

(** ** Target 5: A:g5, the gap-5 contact.

    A:g5 (tools/chunkstep-cases.json) is chunkCascade_w with its `g`
    argument fixed at 1: the contact's gap `[0]^^(4+g)` is `[0]^^5` at
    g = 1, already inside the range mstep_insulate_carryexit/exc_insulate
    cover (no lower bound on g there), so no new machinery is needed --
    only the specialization, with `tail` left open so the contact's run
    and everything deeper pass through untouched, matching the JSON rule
    ("entry becomes [1, run] (deeper untouched)"). Validated against the
    JSON orbit instance (k=0, run=2, no deeper: p 44->42, L 16->24, n=91)
    and four constructed instances varying k (0,1,2), run (1,2,3,4) and
    deeper-tail shape/length (none, one entry, two entries), all exact
    endpoint and step-count matches (task report has the full table). *)

Corollary chunkA_g5 : forall (k p L : nat) (tail : list Sym),
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 (blocks k ([0; 0; 0; 0; 0] ++ tail))))
        (cons 4 (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 (cons 0 tail)))
           (cons (4 * k + 8) (prep p (cons (8 + L) nil)))).
Proof. introv HL. exact (chunkCascade_w k 1 p L tail HL). Qed.

Print Assumptions chunkBig_w.
Print Assumptions chunkBig_w4.
Print Assumptions chunkBig9.
Print Assumptions chunkBig9_4.
Print Assumptions chunkCascade_w.
Print Assumptions mstep_insulate_g3nest.
Print Assumptions lapG3nest.
Print Assumptions blocks_swap.
Print Assumptions chunkA_g3_short.
Print Assumptions chunkA_g3term.
Print Assumptions chunkA_g3.
Print Assumptions chunkA_g5.
