(** * The cost model, checked against the raw machine.

    [sweep_theorem_c] predicts what a sweep costs. [brun] is busycoq's
    bare executor: it runs that many ACTUAL machine steps inside the
    kernel. If it lands on the anchor the model predicts, the cost layer
    is validated against the machine itself, not against
    tools/nhalt.mjs.

    This matters: tools/nhalt-coq.mjs (this model) and tools/nhalt.mjs
    (the older signed-delta model) agree on 167 of N_halt's 170 digits
    and differ by 56. The machine decides which is right. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerBase
                            OdometerCost.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

(** Next string after a sweep: the dip's output, separator restored. *)
Definition nxt (W : list glyph) : list glyph :=
  match dip W with
  | Some (_ :: Z') => gf :: Z'
  | _ => []
  end.

Definition cost1 (W : list glyph) (n : nat) : nat :=
  match dip_cost W with
  | Some k => 16 * S n + 25 + k
  | None => 0
  end.

Definition W1 := nxt W_BASE.
Definition W2 := nxt W1.
Definition W3 := nxt W2.

Definition SWEEP0 : nat := cost1 W_BASE N_TAIL.
Definition SWEEP1 : nat := cost1 W1 (S N_TAIL).
Definition SWEEP2 : nat := cost1 W2 (S (S N_TAIL)).

Eval vm_compute in (dip_cost W_BASE).
Eval vm_compute in SWEEP0.
Eval vm_compute in SWEEP1.
Eval vm_compute in SWEEP2.
Eval vm_compute in (SWEEP0 + SWEEP1 + SWEEP2)%nat.

Definition c1 : Q * ctape :=
  match brun SWEEP0 base_c with Some c => c | None => base_c end.
Definition c3 : Q * ctape :=
  match brun (SWEEP0 + SWEEP1 + SWEEP2) base_c with
  | Some c => c | None => base_c end.

(** ONE sweep: the predicted count lands exactly on the next anchor. *)
Lemma sweep0_lands_on_next_anchor : lift c1 = anchor W1 (S N_TAIL).
Proof. vm_compute. reflexivity. Qed.

(** THREE sweeps: the counts compose, so the model is not accidentally
    right once. *)
Lemma sweep012_lands : lift c3 = anchor W3 (S (S (S N_TAIL))).
Proof. vm_compute. reflexivity. Qed.
