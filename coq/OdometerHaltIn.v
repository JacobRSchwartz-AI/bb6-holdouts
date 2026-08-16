(** * Assembling halts_in from the blank tape.

    Three pieces, each with its exact count:
      N_BASE     blank tape to the base anchor, by the bare executor
      legs       549 spans-plus-events, by leg_c
      fatal      the dying sweep, by death_sweep_c

    Everything is carried in binary N and the step relation is indexed
    by N.to_nat of it. N_halt has 170 digits; Coq's nat is unary, so no
    literal for it can exist, and the kernel must never normalise the
    index. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerOrbit
                            OdometerCost OdometerSpan OdometerSpanSum
                            OdometerSpanRun OdometerLegCost OdometerDeathCost
                            OdometerBase.
From Coq Require Import Lia NArith.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope N_scope.

(** [brun_sound] is stated at evstep, which throws the count away. The
    same induction keeps it. *)
Lemma brun_sound_c : forall k c c',
  brun k c = Some c' -> lift c -[ tm ]->> k / lift c'.
Proof.
  induction k; introv H.
  - cbn in H. injection H as <-. apply multistep_0.
  - cbn in H.
    destruct (bstep c) as [c1 |] eqn:E; [| discriminate].
    eapply multistep_S.
    + apply bstep_sound. exact E.
    + eapply IHk. exact H.
Qed.

(** Obligation 1, now counted: the base anchor is exactly N_BASE steps
    from the blank tape. *)
Lemma base_reach_c : c0 -[ tm ]->> N_BASE / anchor W_BASE N_TAIL.
Proof.
  rewrite <- base_lift. rewrite <- lift_starting.
  apply (brun_sound_c N_BASE). exact base_brun.
Qed.

(** Prefixing a counted run onto a counted halt (N-indexed). *)
Lemma halts_in_prefix : forall c c' a b,
  c -[ tm ]->> (N.to_nat a) / c' ->
  halts_in tm c' (N.to_nat b) ->
  halts_in tm c (N.to_nat (a + b)).
Proof.
  intros c c' a b H1 [ch [H2 H3]].
  exists ch. split; [| exact H3].
  rewrite N2Nat.inj_add. eapply multistep_trans; eassumption.
Qed.

Lemma multistep_transN : forall c c' c'' a b,
  c -[ tm ]->> (N.to_nat a) / c' ->
  c' -[ tm ]->> (N.to_nat b) / c'' ->
  c -[ tm ]->> (N.to_nat (a + b)) / c''.
Proof.
  intros. rewrite N2Nat.inj_add. eapply multistep_trans; eassumption.
Qed.

(** The fatal sweep, N-indexed, for the end of the chain. *)
Lemma death_sweep_cN : forall Z m k,
  dies_cost (gf :: Z) = Some (N.to_nat k) ->
  halts_in tm (anchor (gf :: Z) (N.to_nat m))
    (N.to_nat (4 * m + 9 + k)).
Proof.
  intros Z m k Hk.
  replace (N.to_nat (4 * m + 9 + k))
    with (4 + (1 + (4 * S (N.to_nat m) + N.to_nat k)))%nat
    by (rewrite !N2Nat.inj_add, !N2Nat.inj_mul;
        cbn [N.to_nat Pos.to_nat Pos.iter_op]; lia).
  apply death_sweep_c. exact Hk.
Qed.

(** N_BASE as an N, so the whole total can be one N expression. *)
Definition N_BASE_N : N := N.of_nat N_BASE.

Lemma base_reach_cN : c0 -[ tm ]->> (N.to_nat N_BASE_N) / anchor W_BASE N_TAIL.
Proof. unfold N_BASE_N. rewrite Nat2N.id. exact base_reach_c. Qed.
