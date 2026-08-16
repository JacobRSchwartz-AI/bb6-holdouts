(** * The cost model, checked against the raw machine.

    [sweep_theorem_c] predicts that one sweep out of the base anchor
    costs [16 * S N_TAIL + 25 + dip_cost W_BASE] raw steps. [brun] is
    busycoq's bare executor: it runs that many ACTUAL machine steps
    inside the kernel. If it lands exactly on the next anchor, the cost
    layer is validated against the machine itself, not against
    tools/nhalt.mjs. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerBase
                            OdometerCost.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Eval vm_compute in (dip_cost W_BASE).

Definition SWEEP0 : nat :=
  match dip_cost W_BASE with
  | Some k => 16 * S N_TAIL + 25 + k
  | None => 0
  end.

Eval vm_compute in SWEEP0.

(** The next anchor's string: the dip's output with the separator
    restored, exactly as [sweep_theorem_c] states it. *)
Definition W1 : list glyph :=
  match dip W_BASE with
  | Some (_ :: Z') => gf :: Z'
  | _ => []
  end.

Definition c1 : Q * ctape :=
  match brun SWEEP0 base_c with
  | Some c => c
  | None => base_c
  end.

(** THE CHECK: SWEEP0 raw steps land on the next anchor. *)
Lemma sweep0_lands_on_next_anchor : lift c1 = anchor W1 (S N_TAIL).
Proof. vm_compute. reflexivity. Qed.
