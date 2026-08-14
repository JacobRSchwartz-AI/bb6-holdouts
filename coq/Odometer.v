(** * The Odometer: 1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA *)

(** BB(6) holdout. Non-halt argument: notes/odometer.md in this repo.
    Proof plan (M4): startup -> structured-era sweep lemmas -> the descent
    -> crisis -> regime-3 sweep lemmas -> the melt lemma -> stationary
    meta-cycle W(n) -->+ W(n+1), closed by progress_nonhalt_simple. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, C)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, R, E)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (1, L, F)
  | D, 0 => None            | D, 1 => Some (0, L, E)
  | E, 0 => Some (1, R, B)  | E, 1 => Some (0, R, B)
  | F, 0 => Some (0, L, F)  | F, 1 => Some (1, L, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** The anchor: state C at the right edge of the written tape, facing the
    blank half. All macro-level bookkeeping (SPELL, the clock) is stated at
    anchors; ground truth from tools/regime3b.mjs and friends. *)

Lemma startup : c0 -->* const 0 <* <[1; 1; 0; 1; 0; 1; 1; 1] {{C}}> const 0.
Proof. execute. Qed.

(** Raw shift rules — the atoms the k=4 glyph lemmas compile down to. *)

(** B eats 11-pairs rightward, leaving 10-pairs: the O-glyph writer. *)
Lemma B_pairs : forall n l r,
  l {{B}}> [1; 1]^^n *> r -->* l <* <[1; 0]^^n {{B}}> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (0 >> 1 >> ([0; 1]^^n *> l)) with ([0; 1] *> [0; 1]^^n *> l).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** F slides leftward over zeros unchanged. *)
Lemma F_zeros : forall n l r,
  l <* <[0]^^n <{{F}} r -->* l <{{F}} [0]^^n *> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (0 >> ([0]^^n *> r)) with ([0] *> [0]^^n *> r).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.
