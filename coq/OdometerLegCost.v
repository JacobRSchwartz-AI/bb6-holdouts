(** * One leg of the ledger, with its exact step count.

    The orbit alternates parametric spans (the carry stays inside the
    zone, [sweep_span_c]) with 549 concrete EVENT dips (the carry
    escapes into the tail, so the string changes shape and the cost is
    read off by vm_compute). A leg is one span plus the event that ends
    it. Everything is carried in binary N: the tail clock alone runs to
    3*2^279 and no nat literal can express that. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerOrbit
                            OdometerCost OdometerSpan OdometerSpanSum
                            OdometerSpanRun.
From Coq Require Import Lia NArith.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope N_scope.

(** Sweeps in the span, then the event sweep itself. *)
Definition legcost (G : nat) (v m k : N) : N :=
  spancost G v (16 ^ N.of_nat G - 1 - v) m
  + (16 * (m + (16 ^ N.of_nat G - 1 - v) + 1) + 25 + k).

Lemma leg_c : forall G v T Z' k m,
  v < 16 ^ N.of_nat G ->
  dip (spellW G (16 ^ N.of_nat G - 1) T) = Some (gO :: Z') ->
  dip_cost (spellW G (16 ^ N.of_nat G - 1) T) = Some (N.to_nat k) ->
  anchor (spellW G v T) (N.to_nat m)
  -[ tm ]->> (N.to_nat (legcost G v m k))
  / anchor (gf :: Z') (N.to_nat (m + (16 ^ N.of_nat G - v))).
Proof.
  intros G v T Z' k m Hv Hdip Hk.
  pose proof (N.pow_nonzero 16 (N.of_nat G) ltac:(discriminate)) as Hnz.
  unfold legcost.
  set (n := 16 ^ N.of_nat G - 1 - v) in *.
  assert (Hn : v + N.of_nat (N.to_nat n) <= 16 ^ N.of_nat G - 1)
    by (rewrite N2Nat.id; unfold n; lia).
  rewrite N2Nat.inj_add.
  eapply multistep_trans.
  - replace (spancost G v n m)
      with (spancost G v (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat m)))
      by (rewrite !N2Nat.id; reflexivity).
    apply (sweep_span_c (N.to_nat n) G v T (N.to_nat m) Hn).
  - rewrite N2Nat.id.
    (* the span left the counter at all-ones; the event fires there *)
    replace (v + n) with (16 ^ N.of_nat G - 1) by (unfold n; lia).
    replace (N.to_nat m + N.to_nat n)%nat with (N.to_nat (m + n))
      by (rewrite N2Nat.inj_add; reflexivity).
    replace (N.to_nat (m + (16 ^ N.of_nat G - v)))
      with (S (N.to_nat (m + n)))
      by (replace (m + (16 ^ N.of_nat G - v)) with ((m + n) + 1)
            by (unfold n; lia);
          rewrite N2Nat.inj_add;
          cbn [N.to_nat Pos.to_nat Pos.iter_op]; lia).
    replace (N.to_nat (16 * (m + n + 1) + 25 + k))
      with (16 * S (N.to_nat (m + n)) + 25 + N.to_nat k)%nat
      by (rewrite !N2Nat.inj_add, !N2Nat.inj_mul;
          cbn [N.to_nat Pos.to_nat Pos.iter_op]; lia).
    unfold spellW.
    apply sweep_theorem_c.
    + rewrite <- Hdip. unfold spellW. reflexivity.
    + rewrite <- Hk. unfold spellW. reflexivity.
Qed.
