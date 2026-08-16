(** * Summing a span.

    A leg of the ledger runs the counter from v up to 16^G - 1: that is
    16^G - 1 - v sweeps, at values v, v+1, ..., 16^G - 2. Sweep i costs

      16 * (m + i + 1) + 25 + 20 + zwcost G (v + i)

    (tail passes, the two edge turnarounds, entering the zone, and the
    group walk). Summing gives three pieces:

      16 * (n*m + tri n + n)      the tail passes, a triangular number
      45 * n                      the fixed part
      spanBelow G (v+n) - spanBelow G v    the group walks

    [spanBelow G X] is the total group-walk cost of every value below X.
    It recurses on G, NOT on X, so it evaluates in at most G steps even
    when X has 85 digits. That is the whole reason this is tractable:
    nhalt.mjs's closed form S(X, G) counts values with exactly j
    trailing 15s via floor division, which would need a real
    number-theoretic argument in Coq. This needs one succ lemma. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerOrbit
                            OdometerCost OdometerSpan.
From Coq Require Import Lia NArith.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope N_scope.

(** Partial sums of [fbyte] over the terminating bytes. *)
Definition Fpre (d : N) : N :=
  match d with
  | 0 => 0   | 1 => 7   | 2 => 18  | 3 => 25
  | 4 => 44  | 5 => 51  | 6 => 62  | 7 => 69
  | 8 => 92  | 9 => 99  | 10 => 110 | 11 => 117
  | 12 => 136 | 13 => 143 | 14 => 154 | _ => 161
  end.

(** One full digit's worth: all fifteen terminating bytes (161) plus
    the 24 charged when the digit is 15 and the carry goes deeper. *)
Definition DIGIT : N := 185.

Fixpoint spanBelow (G : nat) (v : N) : N :=
  match G with
  | O => 0
  | S G' => (v / 16) * DIGIT + spanBelow G' (v / 16) + Fpre (v mod 16)
  end.

(** * The key lemma: spanBelow advances by exactly one dip's group cost. *)

Lemma spanBelow_succ : forall G v,
  spanBelow G (v + 1) = spanBelow G v + N.of_nat (zwcost G v).
Proof.
  induction G as [| G' IH]; intro v.
  - cbn. reflexivity.
  - assert (Hlt := byte_lt v).
    destruct (N.eq_dec (v mod 16) 15) as [H15 | Hne].
    + (* the carry: high part increments, low digit wraps to 0 *)
      destruct (byte_C v H15) as [Hm Hd].
      cbn [spanBelow zwcost]. rewrite Hm, Hd, H15.
      cbn [N.eqb Pos.eqb]. rewrite IH.
      unfold Fpre, DIGIT. lia.
    + (* no carry: high part fixed, low digit steps *)
      assert (Hb : v mod 16 < 15) by lia.
      destruct (byte_S v (v mod 16) eq_refl Hb) as [Hm Hd].
      cbn [spanBelow zwcost]. rewrite Hm, Hd.
      assert (Hnb : (v mod 16 =? 15) = false) by (apply N.eqb_neq; lia).
      rewrite Hnb.
      assert (Hc : v mod 16 = 0 \/ v mod 16 = 1 \/ v mod 16 = 2 \/
                   v mod 16 = 3 \/ v mod 16 = 4 \/ v mod 16 = 5 \/
                   v mod 16 = 6 \/ v mod 16 = 7 \/ v mod 16 = 8 \/
                   v mod 16 = 9 \/ v mod 16 = 10 \/ v mod 16 = 11 \/
                   v mod 16 = 12 \/ v mod 16 = 13 \/ v mod 16 = 14) by lia.
      destruct Hc as
        [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]]]]]]]]]];
        rewrite Hq; cbn; lia.
Qed.

(** * The triangular number, for the tail passes. *)

Definition tri (n : N) : N := n * (n - 1) / 2.

Lemma tri_succ : forall n : N, tri (n + 1) = tri n + n.
Proof.
  intro n. unfold tri.
  assert (E : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n) by nia.
  rewrite E.
  assert (H2 : exists q, n * (n - 1) = 2 * q).
  { destruct (N.Even_or_Odd n) as [[q Hq] | [q Hq]]; subst.
    - exists (q * (2 * q - 1)). nia.
    - exists ((2 * q + 1) * q). nia. }
  destruct H2 as [q Hq]. rewrite Hq.
  replace (2 * q + 2 * n) with ((q + n) * 2) by lia.
  replace (2 * q) with (q * 2) by lia.
  rewrite !N.div_mul by discriminate.
  reflexivity.
Qed.

(** * The cost of a whole span. *)

Definition spancost (G : nat) (v : N) (n m : N) : N :=
  16 * (n * m + tri n + n) + 45 * n
  + (spanBelow G (v + n) - spanBelow G v).

(** Monotonicity of spanBelow, so the subtraction above is honest
    (N truncates, so we must know the larger term really is larger). *)
Lemma spanBelow_mono_succ : forall G v,
  spanBelow G v <= spanBelow G (v + 1).
Proof. intros. rewrite spanBelow_succ. lia. Qed.

Lemma spanBelow_mono : forall G n v,
  spanBelow G v <= spanBelow G (v + N.of_nat n).
Proof.
  induction n; intros v.
  - cbn. rewrite N.add_0_r. lia.
  - replace (v + N.of_nat (S n)) with ((v + 1) + N.of_nat n) by lia.
    pose proof (spanBelow_mono_succ G v).
    pose proof (IHn (v + 1)). lia.
Qed.

(** [spancost] steps the way the sweeps do. *)
Lemma spancost_succ : forall G v n m,
  spancost G v (n + 1) m
  = (16 * (m + 1) + 45 + N.of_nat (zwcost G v)) + spancost G (v + 1) n (m + 1).
Proof.
  intros. unfold spancost.
  rewrite tri_succ.
  replace (v + 1 + n) with (v + (n + 1)) by lia.
  pose proof (spanBelow_succ G v) as HS.
  pose proof (spanBelow_mono G (N.to_nat n) (v + 1)) as HM.
  rewrite N2Nat.id in HM.
  replace (v + 1 + n) with (v + (n + 1)) in HM by lia.
  lia.
Qed.
