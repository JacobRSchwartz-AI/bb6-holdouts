(** * The Parity machine: 1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA *)

(** BB(6) holdout. Non-halt campaign notes: notes/parity.md in this repo.
    The only halt rule is E reading 1. E occurs only inside the D/E left
    fill scan, which crosses a zero-gap writing 1s, alternating D,E,D,E
    starting in D; it exits safely (D reads the terminating 1) iff the gap
    has even length. The proof shows every gap the scan ever crosses is
    even, via an inductive configuration invariant, closed by
    progress_nonhalt. This file: the machine and the four scan atoms. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, L, F)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, R, B)
  | C, 0 => Some (0, R, D)  | C, 1 => Some (0, R, C)
  | D, 0 => Some (1, L, E)  | D, 1 => Some (1, L, F)
  | E, 0 => Some (1, L, D)  | E, 1 => None
  | F, 0 => Some (0, L, B)  | F, 1 => Some (1, L, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** The four scan atoms.

    B: rightward over 1s, preserving.
    C: rightward over 1s, erasing to 0.
    D/E: leftward over 0-PAIRS, filling with 1s (D first; even gap = safe).
    F/A: leftward over 1-PAIRS, F preserves the near cell, A erases the far
    one: tape pair 11 becomes 01. *)

Lemma B_ones : forall n l r,
  l {{B}}> [1]^^n *> r -->* l <* <[1]^^n {{B}}> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (1 >> ([1]^^n *> l)) with ([1] *> [1]^^n *> l).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

Lemma C_ones : forall n l r,
  l {{C}}> [1]^^n *> r -->* l <* <[0]^^n {{C}}> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (0 >> ([0]^^n *> l)) with ([0] *> [0]^^n *> l).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

Lemma DE_fill : forall n l r,
  l <* <[0; 0]^^n <{{D}} r -->* l <{{D}} [1; 1]^^n *> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (1 >> 1 >> ([1; 1]^^n *> r)) with ([1; 1] *> [1; 1]^^n *> r).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

Lemma FA_halve : forall n l r,
  l <* <[1; 1]^^n <{{F}} r -->* l <{{F}} [0; 1]^^n *> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (0 >> 1 >> ([0; 1]^^n *> r)) with ([0; 1] *> [0; 1]^^n *> r).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** F slides leftward over 0s unchanged? No: F0 exits to B immediately.
    The remaining single-step turns (B0, C0, D1, F0, A0, A1) are consumed
    inline by execute in the composed lemmas. *)

(** ** Phase transitions: scan + turn, still context-generic. *)

(** B runs right over n ones, hits a 0, writes 1, hands to C. *)
Lemma B_phase : forall n l r,
  l {{B}}> [1]^^n *> 0 >> r -->* l <* <[1]^^n <* <[1] {{C}}> r.
Proof.
  introv. follow B_ones. execute.
Qed.

(** C erases n ones rightward, hits a 0, writes 0, hands to D. *)
Lemma C_phase : forall n l r,
  l {{C}}> [1]^^n *> 0 >> r -->* l <* <[0]^^n <* <[0] {{D}}> r.
Proof.
  introv. follow C_ones. execute.
Qed.

(** The fill scan proper: D at the right end of a zero-run of even length,
    fills it with 1s, reads the terminating 1 in D (SAFE), hands to F.
    This is the lemma whose hypothesis shape encodes the whole nonhalt
    argument: the gap is 2n, never odd. *)
Lemma D_phase : forall n l r,
  l <* <[1] <* <[0; 0]^^n <{{D}} r -->* l <{{F}} 1 >> [1; 1]^^n *> r.
Proof.
  introv. follow DE_fill. execute.
Qed.

(** The halving scan exits two ways.

    Even 1-run (n pairs), then F reads 0: F0 writes 0, steps left into B,
    which bounces off a 1 and heads back right. *)
Lemma F_exit_even : forall n l r,
  l <* <[1] <* <[0] <* <[1; 1]^^n <{{F}} r -->*
  l <* <[1] {{B}}> 0 >> [0; 1]^^n *> r.
Proof.
  introv. follow FA_halve. execute.
Qed.

(** Odd 1-run (n pairs + 1), then A reads the 0 beyond: A0 writes 1 and
    turns right into B directly. *)
Lemma F_exit_odd : forall n l r,
  l <* <[0] <* <[1] <* <[1; 1]^^n <{{F}} r -->*
  l <* <[1] {{B}}> 1 >> [0; 1]^^n *> r.
Proof.
  introv. follow FA_halve. execute.
Qed.

(** ** The micro-cycle.

    At the fill boundary the machine shuffles one 01-pair into the solid
    1-run: anchor F about to read the gap 0, left of it the run's trailing
    0. Ground truth: anchor-config.mjs at steps 20003/20013. One micro-step
    consumes the leading pair of the 01-region and grows the left 1-run by
    two, preserving the anchor shape. *)

Lemma micro_step : forall l r,
  l <* <[0] {{F}}> [0; 1; 0; 1] *> r -->*
  l <* <[1; 1] <* <[0] {{F}}> [0; 1] *> r.
Proof. execute. Qed.

(** The whole 01-region is consumed pair by pair, two 1s deposited per
    pair, anchor shape preserved, until two pairs remain. *)
Lemma micro_all : forall k l r,
  l <* <[0] {{F}}> [0; 1]^^k *> [0; 1; 0; 1] *> r -->*
  l <* <[1; 1]^^k <* <[0] {{F}}> [0; 1; 0; 1] *> r.
Proof.
  induction k; introv.
  - finish.
  - change ([0; 1]^^(S k) *> [0; 1; 0; 1] *> r)
      with ([0; 1] *> [0; 1]^^k *> [0; 1] *> [0; 1] *> r).
    rewrite lpow_shift'.
    follow micro_step.
    rewrite <- lpow_shift'.
    change ([0; 1]^^k *> [0; 1] *> [0; 1] *> r)
      with ([0; 1]^^k *> [0; 1; 0; 1] *> r).
    follow IHk.
    rewrite lpow_shift'. finish.
Qed.

(** ** Sub-era glue.

    Launch entry: from the A-turn, six steps consume the first two pairs
    and land exactly on the micro-cycle F-anchor. Ground truth: raw trace
    s20467-20473. *)
Lemma launch_entry : forall l r,
  l {{A}}> [0; 1; 0; 1; 0; 1] *> r -->*
  l <* <[1; 1; 1] <* <[0] {{F}}> [0; 1] *> r.
Proof. execute. Qed.

(** E-first fill pairs: the refill scan after the punch-through runs E,D
    per zero-pair (the fresh D0 cell is consumed separately). *)
Lemma ED_fill : forall n l r,
  l <* <[0; 0]^^n <{{E}} r -->* l <{{E}} [1; 1]^^n *> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (1 >> 1 >> ([1; 1]^^n *> r)) with ([1; 1] *> [1; 1]^^n *> r).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** Junction: from the micro-cycle anchor with exactly two pairs left,
    the shuffle consumes both pairs and the separator, deposits six 1s,
    and hands C the block face. *)
Lemma junction : forall l r,
  l <* <[0] {{F}}> [0; 1] *> [0; 1] *> [0] *> [1] *> r -->*
  l <* <[1; 1; 1; 1; 1; 1] {{C}}> [1] *> r.
Proof. execute. Qed.

Lemma lpow_pair : forall (x : Sym) m, [x; x]^^m = [x]^^(2 * m).
Proof.
  induction m.
  - reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    simpl. rewrite IHm. reflexivity.
Qed.

Lemma ones_comm : forall m (r : Stream Sym),
  [1; 1]^^m *> 1 >> r = 1 >> [1; 1]^^m *> r.
Proof.
  introv. rewrite lpow_pair.
  change (1 >> r) with ([1] *> r).
  rewrite lpow_shift'. reflexivity.
Qed.

(** The punch-through and refill: C erases the even block, the fill scan
    crosses the even gap (never reading a 1 in state E: the parity
    argument), exits safely on the junction 1, and hands F the halving. *)
Lemma punch_refill : forall m l,
  l <* <[1] {{C}}> [1]^^(2 * m) *> const 0 -->*
  l <{{F}} 1 >> 1 >> [1; 1]^^m *> 1 >> const 0.
Proof.
  introv.
  follow C_ones.
  execute.
  rewrite <- Str_app_assoc.
  rewrite <- lpow_add.
  replace (m + m) with (2 * m) by lia.
  rewrite <- lpow_pair.
  follow DE_fill.
  execute.
  rewrite ones_comm. finish.
Qed.

Lemma ones_join : forall a b (l : Stream Sym),
  l <* <[1]^^b <* <[1]^^a = l <* <[1]^^(a + b).
Proof.
  introv. rewrite <- Str_app_assoc. rewrite <- lpow_add. reflexivity.
Qed.

(** ** The half-period core: from a deep A-turn, the machine consumes the
    whole pair region (launch + micros + junction), punches through and
    refills the right block, halves the deposited run, and arrives at the
    wall face in state F with the same pair count and a block grown by 2. *)
Lemma sweep_core : forall k m l,
  l {{A}}> [0; 1]^^(k + 5) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  l <{{F}} [0; 1]^^(k + 5) *> [1] *> [1] *> [1; 1]^^(m + 1) *> [1] *> const 0.
Proof.
  introv.
  (* peel three literal pairs for the launch *)
  replace (k + 5) with (3 + (k + 2)) by lia.
  rewrite lpow_add, Str_app_assoc.
  follow launch_entry.
  (* reshape: [0;1] *> [0;1]^^(k+2) *> Z  ==>  [0;1]^^(k+1) *> [0;1;0;1] *> Z *)
  rewrite <- lpow_shift'.
  replace (k + 2) with (k + 1 + 1) by lia.
  rewrite lpow_add, Str_app_assoc.
  change ([0; 1]^^1 *> [0; 1] *> [0] *> [1]^^(2 * m + 2) *> const 0)
    with ([0; 1; 0; 1] *> [0] *> [1]^^(2 * m + 2) *> const 0).
  follow micro_all.
  (* expose the junction shape: last two pairs + separator + first block 1 *)
  replace (2 * m + 2) with (S (2 * m + 1)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow junction.
  (* left: peel the junction marker; right: refold the block *)
  change (l <* <[1; 1; 1] <* <[1; 1]^^(k + 1) <* <[1; 1; 1; 1; 1; 1])
    with (l <* <[1; 1; 1] <* <[1; 1]^^(k + 1) <* <[1]^^5 <* <[1]).
  change ([1] *> [1]^^(2 * m + 1) *> const 0)
    with ([1]^^(S (2 * m + 1)) *> const 0).
  replace (S (2 * m + 1)) with (2 * (m + 1)) by lia.
  follow punch_refill.
  (* normalize the all-ones run and halve it *)
  change ([1; 1; 1] *> l) with ([1]^^3 *> l).
  rewrite lpow_pair.
  rewrite !ones_join.
  replace (5 + 2 * (k + 1) + 3) with (2 * (k + 5)) by lia.
  rewrite <- lpow_pair.
  follow FA_halve.
  rewrite <- !lpow_add.
  replace (3 + (k + 1 + 1)) with (k + 5) by lia.
  finish.
Qed.

(** ** Startup: c0 to the first structured configuration. *)

Lemma startup : c0 -->* const 0 <* <[1] {{B}}> [1; 1; 1; 1] *> const 0.
Proof. execute. Qed.
