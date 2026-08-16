(** * A whole span of sweeps, with its exact step count.

    Composes [sweep_theorem_c] across all 16^G - 1 - v sweeps of a
    counting era. The count is [spancost], which is closed-form: it
    evaluates in at most G steps no matter how astronomically many
    sweeps the span contains. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerOrbit
                            OdometerCost OdometerSpan OdometerSpanSum.
From Coq Require Import Lia NArith.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope N_scope.

Lemma multistep_0'' : forall c c', c = c' -> c -[ tm ]->> 0 / c'.
Proof. intros. subst c'. apply multistep_0. Qed.

(** Inside a span every value is below the top, so no dip escapes into
    the tail and [dip_spell] / [dip_cost_spell] both apply. *)
Lemma span_lt_ne : forall G v,
  v < 16 ^ N.of_nat G - 1 ->
  v mod 16 ^ N.of_nat G <> 16 ^ N.of_nat G - 1.
Proof.
  intros G v Hlt.
  pose proof (N.pow_nonzero 16 (N.of_nat G) ltac:(discriminate)).
  rewrite N.mod_small by lia. lia.
Qed.

(** One sweep of a span, with its count. *)
Lemma sweep_spell_c : forall G v T m,
  v < 16 ^ N.of_nat G - 1 ->
  anchor (spellW G v T) m
  -[ tm ]->> (16 * S m + 25 + zcost G v)%nat
  / anchor (spellW G (v + 1) T) (S m).
Proof.
  intros G v T m Hlt.
  pose proof (span_lt_ne G v Hlt) as Hne.
  unfold spellW.
  apply sweep_theorem_c.
  - rewrite <- (dip_spell G v T Hne). unfold spellW. reflexivity.
  - rewrite <- (dip_cost_spell G v T Hne). unfold spellW. reflexivity.
Qed.

(** The whole span. *)
Lemma sweep_span_c : forall n G v T m,
  v + N.of_nat n <= 16 ^ N.of_nat G - 1 ->
  anchor (spellW G v T) m
  -[ tm ]->> (N.to_nat (spancost G v (N.of_nat n) (N.of_nat m)))
  / anchor (spellW G (v + N.of_nat n) T) (m + n).
Proof.
  induction n; intros G v T m Hle.
  - replace (N.of_nat 0) with 0 by reflexivity.
    (* lia cannot see through tri's division, so discharge tri 0 first *)
    assert (Hz : spancost G v 0 (N.of_nat m) = 0).
    { unfold spancost.
      replace (tri 0) with 0 by (unfold tri; reflexivity).
      replace (v + 0) with v by lia. lia. }
    rewrite Hz.
    replace (v + 0) with v by lia.
    replace (m + 0)%nat with m by lia.
    cbn [N.to_nat]. apply multistep_0''. reflexivity.
  - assert (Hlt : v < 16 ^ N.of_nat G - 1) by lia.
    replace (N.of_nat (S n)) with (N.of_nat n + 1) by lia.
    rewrite spancost_succ.
    rewrite N2Nat.inj_add.
    eapply multistep_trans.
    + replace (N.to_nat (16 * (N.of_nat m + 1) + 45 + N.of_nat (zwcost G v)))
        with (16 * S m + 25 + zcost G v)%nat
        by (unfold zcost; rewrite !N2Nat.inj_add, !N2Nat.inj_mul;
            cbn [N.to_nat Pos.to_nat Pos.iter_op]; rewrite !Nat2N.id; lia).
      apply sweep_spell_c. exact Hlt.
    + replace (N.of_nat m + 1) with (N.of_nat (S m)) by lia.
      replace (v + (N.of_nat n + 1)) with (v + 1 + N.of_nat n) by lia.
      replace (m + S n)%nat with (S m + n)%nat by lia.
      apply IHn. lia.
Qed.
