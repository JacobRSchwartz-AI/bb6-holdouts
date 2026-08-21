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
From Coq Require Import PeanoNat.
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

Lemma lpow_push : forall (x : Sym) n (r : Stream Sym),
  [x]^^n *> x >> r = x >> [x]^^n *> r.
Proof.
  induction n; introv.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma ones_succ : forall n (r : Stream Sym),
  [1] *> [1]^^n *> r = [1]^^(n + 1) *> r.
Proof.
  introv. rewrite lpow_add, Str_app_assoc, lpow_shift'. reflexivity.
Qed.

Lemma pow_succ : forall (xs : list Sym) n (r : Stream Sym),
  xs *> xs^^n *> r = xs^^(n + 1) *> r.
Proof.
  introv. replace (n + 1) with (S n) by lia.
  rewrite lpow_S, Str_app_assoc. reflexivity.
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

(** ** The full half-period, odd-exit form: when the wall face under the
    halving run is `.. 0 1` (the low bit-pair's top), the run is odd, the
    scan swallows the 1, and the A0 turn writes its partner: the odometer
    bit write IS the F_exit_odd ending. The machine relaunches in B over
    the freshly halved pair region. *)
Lemma sweep_A_odd : forall k m l,
  l <* <[0] <* <[1] {{A}}> [0; 1]^^(k + 5) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  l <* <[1] {{B}}> 1 >> [0; 1]^^(k + 5) *> [1] *> [1] *> [1; 1]^^(m + 1) *> [1] *> const 0.
Proof.
  introv.
  follow sweep_core.
  (* the halved pairs were emitted by FA_halve inside sweep_core; re-split
     them is not needed: F now faces the wall top `.. 0 1`. One F1 step
     and the A0 turn close it. *)
  execute.
Qed.

(** ** The increment excursion (the F0 deep turn's wall write).

    CS body: 9 steps. F consumes two wall zeros, B0 writes a 1, the CTX-2
    fill (gap exactly 2) absorbs into it; F emerges two cells deeper. *)
Lemma cs_body : forall l r,
  l <* <[0; 0] <{{F}} 0 >> r -->* l <{{F}} 1 >> 1 >> 1 >> r.
Proof. execute. Qed.

(** Carry: the occupied slot pair under F is halved (= FA_halve n=1),
    clearing the high cell; F emerges four cells deeper with the slot's
    low cell exposed for the terminal erase. Already provable directly. *)
Lemma carry_step : forall l r,
  l <* <[1; 1] <{{F}} r -->* l <{{F}} [0; 1] *> r.
Proof.
  introv. exact (FA_halve 1 l r).
Qed.

(** R1 tail: F meets an empty slot; two B0 writes set the bit pair, the
    terminal C-erase clears the scratch and the excursion hands the head
    to the micro-train at a standard micro anchor. Ground truth: raw
    steps s8018-s8035 (B1 transcript, R1 instance). *)
Lemma r1_tail : forall l r,
  l <* <[0; 0] <{{F}} [1; 1; 1] *> [1; 0] *> [1; 0] *> [1; 0] *> r -->*
  l <* <[1; 1] <* <[0; 0; 0] <* <[1; 1] <* <[0] {{F}}> [0; 1] *> [0] *> r.
Proof. execute. Qed.

(** Bit set: F meets the empty slot with the CS junk to its right; two
    B0 writes set the bit pair and C emerges facing the junk. 8 steps. *)
Lemma bitset : forall l r,
  l <* <[0; 0] <{{F}} 1 >> r -->* l <* <[1; 1] {{C}}> 1 >> r.
Proof. execute. Qed.

(** Train handoff: after the terminal erase, the head re-enters the pair
    region and settles on a standard micro anchor. *)
Lemma tail_train : forall l r,
  l <* <[0] {{C}}> [0; 1; 0; 1] *> r -->*
  l <* <[1; 1] <* <[0] {{F}}> [0; 1] *> r.
Proof. execute. Qed.

(** The carry chain: d occupied slots are cleared one by one, each by a
    CS body plus a 2-halving; the junk left behind is solid 1s of length
    4d+3. The 4-cell slot pitch is derived here, not assumed. *)
Lemma excursion_chain : forall d l r,
  l <* ([1; 1] ++ [0; 0])^^d <* <[0; 0] <{{F}} 0 >> r -->*
  l <{{F}} [1]^^(4 * d + 3) *> r.
Proof.
  induction d; introv.
  - follow cs_body. finish.
  - rewrite lpow_S, Str_app_assoc.
    follow cs_body.
    follow carry_step.
    follow IHd.
    replace (4 * S d + 3) with (S (S (S (S (4 * d + 3))))) by lia.
    rewrite !lpow_push. finish.
Qed.

(** The full increment: carry chain, bit set, terminal erase of the junk
    plus the first pair, handing the head to the micro train at a standard
    micro anchor. This is R1 and R2 at every carry depth d in one
    statement: d occupied slots are cleared, slot d is set, and the wall's
    zero field ends up 4d+4 wide. *)
Lemma incr_full : forall d l r,
  l <* <[0; 0] <* ([1; 1] ++ [0; 0])^^d <* <[0; 0] <{{F}}
    0 >> [1; 0] *> [1; 0] *> [1] *> r -->*
  l <* <[1; 1] <* [0]^^(4 * d + 4) {{F}}> [0; 1; 0; 1] *> r.
Proof.
  introv.
  follow excursion_chain.
  replace (4 * d + 3) with (S (4 * d + 2)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow bitset.
  change ([1; 0] *> [1; 0] *> [1] *> r) with (1 >> 0 >> [1; 0] *> [1] *> r).
  rewrite lpow_push.
  change (1 >> 1 >> [1]^^(4 * d + 2) *> 0 >> [1; 0] *> [1] *> r)
    with ([1]^^(S (S (4 * d + 2))) *> 0 >> [1; 0] *> [1] *> r).
  replace (S (S (4 * d + 2))) with (4 * d + 4) by lia.
  follow C_phase.
  execute.
Qed.

(** ** The F-half period: from the micro anchor the increment hands over,
    through the micro train, junction, punch-through, even refill and the
    halving, to the face of the wall. Mirror of sweep_core with no launch
    (the increment already placed the head on a micro anchor). *)
Lemma sweep_F : forall k m l,
  l <* <[0] {{F}}> [0; 1]^^(k + 2) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  l <* <[1] <{{F}} [0; 1]^^(k + 2) *> [1] *> [1] *> [1; 1]^^(m + 1)
    *> [1] *> const 0.
Proof.
  introv.
  rewrite lpow_add, Str_app_assoc.
  change ([0; 1]^^2 *> [0] *> [1]^^(2 * m + 2) *> const 0)
    with ([0; 1; 0; 1] *> [0] *> [1]^^(2 * m + 2) *> const 0).
  follow micro_all.
  replace (2 * m + 2) with (S (2 * m + 1)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow junction.
  change (l <* <[1; 1]^^k <* <[1; 1; 1; 1; 1; 1])
    with (l <* <[1; 1]^^k <* <[1]^^5 <* <[1]).
  change ([1] *> [1]^^(2 * m + 1) *> const 0)
    with ([1]^^(S (2 * m + 1)) *> const 0).
  replace (S (2 * m + 1)) with (2 * (m + 1)) by lia.
  follow punch_refill.
  rewrite lpow_pair, !ones_join.
  replace (5 + 2 * k) with (2 * (k + 2) + 1) by lia.
  rewrite lpow_add, <- lpow_pair, Str_app_assoc.
  follow FA_halve.
  rewrite <- lpow_add.
  finish.
Qed.

(** ** The recurrence.

    Regrouping the refilled run: the block emitted by a half period is
    solid, so it refolds into a single power of ones. *)
Lemma tail_regroup : forall m (r : Stream Sym),
  [1] *> [1] *> [1; 1]^^(m + 1) *> [1] *> r = [1]^^(2 * m + 5) *> r.
Proof.
  introv.
  replace (2 * m + 5) with (2 + (2 * (m + 1) + 1)) by lia.
  rewrite (lpow_add _ 2 (2 * (m + 1) + 1) [1]), Str_app_assoc.
  rewrite (lpow_add _ (2 * (m + 1)) 1 [1]), Str_app_assoc.
  rewrite <- lpow_pair.
  reflexivity.
Qed.

(** THE INVARIANT STEP. One half period consumes exactly one pair and
    grows the block by exactly four cells. Since the block enters as
    2m+2 and leaves as 2m+6, its length stays even -- and that evenness
    is precisely what the fill scan needs to survive (punch_refill's
    hypothesis). This is `p -> p-1, L -> L+4` of the empirical wall law,
    now a theorem. *)
Lemma half_period : forall k m l,
  l {{A}}> [0; 1]^^(k + 5) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  l <{{F}} [0; 1]^^(k + 4) *> [0] *> [1]^^(2 * m + 6) *> const 0.
Proof.
  introv.
  follow sweep_core.
  rewrite tail_regroup.
  replace (k + 5) with (k + 4 + 1) by lia.
  rewrite lpow_add, Str_app_assoc.
  replace (2 * m + 6) with (S (2 * m + 5)) by lia.
  finish.
Qed.

(** ** Small-p half periods.

    The general half_period needs five pairs (launch three, junction two).
    The last turns of an era have fewer, and their chains differ. p = 4:
    the launch hands straight to the junction, no micro train. *)
Lemma half_period_4 : forall m l,
  l {{A}}> [0; 1]^^4 *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  l <{{F}} [0; 1]^^3 *> [0] *> [1]^^(2 * m + 6) *> const 0.
Proof.
  introv.
  change ([0; 1]^^4 *> [0] *> [1]^^(2 * m + 2) *> const 0)
    with ([0; 1; 0; 1; 0; 1] *> [0; 1] *> [0] *> [1]^^(2 * m + 2) *> const 0).
  follow launch_entry.
  replace (2 * m + 2) with (S (2 * m + 1)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow junction.
  change (l <* <[1; 1; 1] <* <[1; 1; 1; 1; 1; 1])
    with (l <* <[1; 1; 1] <* <[1]^^5 <* <[1]).
  change ([1] *> [1]^^(2 * m + 1) *> const 0)
    with ([1]^^(S (2 * m + 1)) *> const 0).
  replace (S (2 * m + 1)) with (2 * (m + 1)) by lia.
  follow punch_refill.
  change ([1; 1; 1] *> l) with ([1]^^3 *> l).
  rewrite !ones_join.
  replace (5 + 3) with (2 * 4) by lia.
  rewrite <- lpow_pair.
  follow FA_halve.
  change (1 >> 1 >> [1; 1]^^(m + 1) *> 1 >> const 0)
    with ([1] *> [1] *> [1; 1]^^(m + 1) *> [1] *> const 0).
  rewrite tail_regroup.
  replace (2 * m + 6) with (S (2 * m + 5)) by lia.
  finish.
Qed.

(** p = 2: the launch runs straight into the block; seven steps of glue
    hand C the face of it. *)
Lemma p2_glue : forall l r,
  l <* <[0] {{F}}> [0; 1] *> r -->* l <* <[1; 1] {{C}}> [1] *> r.
Proof. execute. Qed.

Lemma half_period_2 : forall m l,
  l {{A}}> [0; 1]^^2 *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  l <{{F}} [0; 1]^^1 *> [0] *> [1]^^(2 * m + 6) *> const 0.
Proof.
  introv.
  replace (2 * m + 2) with (S (2 * m + 1)) by lia.
  rewrite lpow_S, Str_app_assoc.
  change ([0; 1]^^2 *> [0] *> [1] *> [1]^^(2 * m + 1) *> const 0)
    with ([0; 1; 0; 1; 0; 1] *> [1]^^(2 * m + 1) *> const 0).
  follow launch_entry.
  follow p2_glue.
  rewrite ones_succ.
  replace (2 * m + 1 + 1) with (2 * (m + 1)) by lia.
  change (l <* <[1; 1; 1] <* <[1; 1]) with (l <* <[1]^^4 <* <[1]).
  follow punch_refill.
  change ([1]^^4 *> l) with ([1; 1]^^2 *> l).
  follow FA_halve.
  change (1 >> 1 >> [1; 1]^^(m + 1) *> 1 >> const 0)
    with ([1] *> [1] *> [1; 1]^^(m + 1) *> [1] *> const 0).
  rewrite tail_regroup.
  replace (2 * m + 6) with (S (2 * m + 5)) by lia.
  finish.
Qed.

(** ** The era boundary (p = 1).

    The increment still fires, but its terminal erase runs out of pairs,
    so the tail differs from incr_full: C ends on the face of the block
    itself rather than at a micro anchor. 26 concrete steps. *)
Lemma era_incr : forall l r,
  l <* <[0; 0] <* <[0; 0] <{{F}} 0 >> [1; 0] *> [1] *> r -->*
  l <* <[1; 1] <* <[0; 0; 0] <* <[1; 1] {{C}}> [1] *> r.
Proof. execute. Qed.

Lemma ones_succ' : forall n (r : Stream Sym), 1 >> [1]^^n *> r = [1]^^(n + 1) *> r.
Proof. introv. rewrite <- ones_succ. reflexivity. Qed.

(** The shallow A-turn: with no pairs left, the halving scan meets the
    wall after a single one, and A0 writes the cell it lands on. *)
Lemma shallow_A : forall l r,
  l <* <[0] <* <[1] <{{F}} r -->* l <* <[1] {{B}}> 1 >> r.
Proof. execute. Qed.

(** The right edge: B runs off the written tape, writes, and the CTX-2
    fill at the blank turns the head around. *)
Lemma right_edge : forall l,
  l {{B}}> const 0 -->* l <{{F}} 1 >> 1 >> 1 >> const 0.
Proof. execute. Qed.

Lemma f1_to_A : forall l r,
  l <* <[0] <* <[1] <{{F}} r -->* l {{A}}> [0] *> [1] *> r.
Proof. execute. Qed.

(** THE ERA BOUNDARY. With one pair left the block is consumed whole,
    the tape becomes a single solid run, and halving it back rebuilds the
    pair region. The counters reset exactly as the census says:
    p' = L/2 + 2 and L' = 4, with L = 2M+2 so p' = M+3. *)
Lemma era_boundary : forall M l,
  l <* <[0; 0] <* <[0; 0] <{{F}} 0 >> [1; 0] *> [1]^^(2 * M + 2) *> const 0
  -->*
  l <* <[1; 1] <* <[0] {{A}}> [0; 1]^^(M + 3) *> [0] *> [1]^^4 *> const 0.
Proof.
  introv.
  replace (2 * M + 2) with (S (2 * M + 1)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow era_incr.
  rewrite ones_succ.
  replace (2 * M + 1 + 1) with (2 * (M + 1)) by lia.
  change (l <* <[1; 1] <* <[0; 0; 0] <* <[1; 1])
    with (l <* <[1; 1] <* <[0; 0; 0] <* <[1] <* <[1]).
  follow punch_refill.
  change (l <* <[1; 1] <* <[0; 0; 0] <* <[1])
    with (l <* <[1; 1] <* <[0; 0] <* <[0] <* <[1]).
  follow shallow_A.
  (* fold the solid run *)
  rewrite lpow_pair, lpow_push, !ones_succ'.
  follow B_ones.
  follow right_edge.
  (* the run plus the A0 cell is odd: halving leaves one for the A-turn *)
  rewrite lpow_shift', ones_succ.
  replace (2 * (M + 1) + 1 + 1 + 1 + 1 + 1) with (2 * (M + 3) + 1) by lia.
  rewrite lpow_add, <- lpow_pair, Str_app_assoc.
  follow FA_halve.
  follow f1_to_A.
  change ([0] *> [1] *> [0; 1]^^(M + 3) *> 1 >> 1 >> 1 >> const 0)
    with ([0; 1] *> [0; 1]^^(M + 3) *> 1 >> 1 >> 1 >> const 0).
  rewrite <- lpow_shift'.
  finish.
Qed.

(** ** The F-half period with its wall write.

    From a deep F-turn whose counter has d trailing occupied slots: the
    increment excursion clears them and sets slot d, the micro train and
    punch run as usual, and the halving lands on the next A-turn. One
    pair consumed, block grown by four, wall incremented. *)
Lemma f_to_a : forall d k m l,
  l <* <[0; 0] <* ([1; 1] ++ [0; 0])^^d <* <[0; 0] <{{F}}
    [0; 1]^^(k + 3) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  l <* <[1; 1] <* [0]^^(4 * d + 2) {{A}}>
    [0; 1]^^(k + 2) *> [0] *> [1]^^(2 * m + 6) *> const 0.
Proof.
  introv.
  replace (k + 3) with (3 + k) by lia.
  rewrite lpow_add, Str_app_assoc.
  follow incr_full.
  (* fold the two pairs the increment handed back *)
  change ([0; 1; 0; 1] *> [0; 1]^^k *> [0] *> [1]^^(2 * m + 2) *> const 0)
    with ([0; 1]^^2 *> [0; 1]^^k *> [0] *> [1]^^(2 * m + 2) *> const 0).
  rewrite <- (Str_app_assoc ([0; 1]^^2) ([0; 1]^^k)), <- lpow_add.
  replace (2 + k) with (k + 2) by lia.
  (* expose one wall zero for sweep_F's anchor *)
  replace (4 * d + 4) with (S (4 * d + 3)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow sweep_F.
  (* expose one more for the A-turn *)
  replace (4 * d + 3) with (S (4 * d + 2)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow f1_to_A.
  change ([0] *> [1] *> [0; 1]^^(k + 2) *> [1] *> [1] *> [1; 1]^^(m + 1)
          *> [1] *> const 0)
    with ([0; 1] *> [0; 1]^^(k + 2) *>
          ([1] *> [1] *> [1; 1]^^(m + 1) *> [1] *> const 0)).
  rewrite tail_regroup.
  rewrite <- (lpow_shift' _ (k + 2) [0; 1]).
  replace (2 * m + 6) with (S (2 * m + 5)) by lia.
  finish.
Qed.

(** ** The era boundary at any carry depth. *)

Lemma d1_step : forall l r, l <* <[0] {{D}}> [1] *> r -->* l {{F}}> [0; 1] *> r.
Proof. execute. Qed.

Lemma era_incr_d : forall d l r,
  l <* <[0; 0] <* ([1; 1] ++ [0; 0])^^d <* <[0; 0] <{{F}}
    0 >> [1; 0] *> [1] *> r -->*
  l <* <[1; 1] <* [0]^^(4 * d + 3) <* <[1; 1] {{C}}> [1] *> r.
Proof.
  introv.
  follow excursion_chain.
  replace (4 * d + 3) with (S (4 * d + 2)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow bitset.
  (* C erases the junk plus the pair's one: 4d+4 in all *)
  change ([1; 0] *> [1] *> r) with (1 >> 0 >> [1] *> r).
  rewrite lpow_push, !ones_succ'.
  replace (4 * d + 2 + 1 + 1) with (4 * d + 4) by lia.
  follow C_phase.
  follow d1_step.
  replace (4 * d + 4) with (S (4 * d + 3)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow p2_glue.
  replace (S (4 * d + 2)) with (4 * d + 3) by lia.
  finish.
Qed.

Lemma era_boundary_d : forall d M l,
  l <* <[0; 0] <* ([1; 1] ++ [0; 0])^^d <* <[0; 0] <{{F}}
    0 >> [1; 0] *> [1]^^(2 * M + 2) *> const 0 -->*
  l <* <[1; 1] <* [0]^^(4 * d + 1) {{A}}>
    [0; 1]^^(M + 3) *> [0] *> [1]^^4 *> const 0.
Proof.
  introv.
  replace (2 * M + 2) with (S (2 * M + 1)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow era_incr_d.
  rewrite ones_succ.
  replace (2 * M + 1 + 1) with (2 * (M + 1)) by lia.
  change (l <* <[1; 1] <* [0]^^(4 * d + 3) <* <[1; 1])
    with (l <* <[1; 1] <* [0]^^(4 * d + 3) <* <[1] <* <[1]).
  follow punch_refill.
  replace (4 * d + 3) with (S (4 * d + 2)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow shallow_A.
  rewrite lpow_pair, lpow_push, !ones_succ'.
  follow B_ones.
  follow right_edge.
  rewrite lpow_shift', ones_succ.
  replace (2 * (M + 1) + 1 + 1 + 1 + 1 + 1) with (2 * (M + 3) + 1) by lia.
  rewrite lpow_add, <- lpow_pair, Str_app_assoc.
  follow FA_halve.
  replace (4 * d + 2) with (S (4 * d + 1)) by lia.
  rewrite lpow_S, Str_app_assoc.
  follow f1_to_A.
  change ([0] *> [1] *> [0; 1]^^(M + 3) *> 1 >> 1 >> 1 >> const 0)
    with ([0; 1] *> [0; 1]^^(M + 3) *> 1 >> 1 >> 1 >> const 0).
  rewrite <- lpow_shift'.
  finish.
Qed.

(** ** The degenerate CS body.

    At the first F-turn of a new era the wall's set bit sits immediately
    left of the turn cell, so the B-scan preserves it and turns one cell
    to the right: C lands at c+1, the fill reads a 1 at once (gap 0, not
    2), and the excursion is five steps with no carry. This is B1's
    fourth dispatch branch, keyed on tape[c-1] = 1. Raw trace s1173. *)
Lemma degen_cs : forall l r,
  l <* <[1] <* <[0] <{{F}} 0 >> [1] *> r -->*
  l <* <[1; 1] {{F}}> [0; 1] *> r.
Proof. execute. Qed.

(** The degenerate micro step: with a 1 rather than a 0 left of the
    anchor the shuffle takes six steps, not ten, and leaves the standard
    micro anchor behind it. Raw trace s1178-s1183. *)
Lemma degen_micro : forall l r,
  l <* <[1; 1] {{F}}> [0; 1] *> [0; 1] *> r -->*
  l <* <[1; 1; 1] <* <[0] {{F}}> [0; 1] *> r.
Proof. execute. Qed.

(** THE ERA-START F-HALF PERIOD.

    Here the wall's set bit sits against the turn cell, so degen_cs and
    degen_micro deposit ones into the wall and the halving finds FIVE of
    them rather than one. Four are halved into two fresh pairs, so the
    pair count goes UP by one instead of down. That is not an anomaly:
    the exact anchor parse shows P running 17, 18, 17, 18 across deep
    turns while L grows by four every time. L, not P, is the monotone
    quantity, and L stays even, which is all the halt guard needs. *)
Lemma f_to_a_era : forall k m l,
  l <* <[0; 0] <* <[1; 1] <* <[0] <{{F}}
    [0; 1]^^(k + 3) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  l <* <[0] {{A}}>
    [0; 1]^^(k + 4) *> [0] *> [1]^^(2 * m + 6) *> const 0.
Proof.
  introv.
  replace (k + 3) with (1 + (k + 2)) by lia.
  rewrite lpow_add, Str_app_assoc.
  follow degen_cs.
  replace (k + 2) with (1 + (k + 1)) by lia.
  rewrite lpow_add, Str_app_assoc.
  follow degen_micro.
  rewrite pow_succ.
  replace (k + 1 + 1) with (k + 2) by lia.
  follow sweep_F.
  (* five ones on the left: halve four, keep one for the A-turn *)
  follow (FA_halve 2 (l <* <[0; 0] <* <[1])
    ([0; 1]^^(k + 2) *> [1] *> [1] *> [1; 1]^^(m + 1) *> [1] *> const 0)).
  follow f1_to_A.
  change ([0] *> [1] *> [0; 1]^^2 *> [0; 1]^^(k + 2) *> [1] *> [1] *>
          [1; 1]^^(m + 1) *> [1] *> const 0)
    with ([0; 1] *> [0; 1]^^2 *> [0; 1]^^(k + 2) *>
          ([1] *> [1] *> [1; 1]^^(m + 1) *> [1] *> const 0)).
  rewrite tail_regroup.
  rewrite <- (Str_app_assoc ([0; 1]^^2) ([0; 1]^^(k + 2))), <- lpow_add.
  replace (2 + (k + 2)) with (k + 4) by lia.
  rewrite <- (lpow_shift' _ (k + 4) [0; 1]).
  replace (2 * m + 6) with (S (2 * m + 5)) by lia.
  finish.
Qed.

(** ** The wall as a binary odometer.

    Slot k of the counter occupies four cells at offset 4k+2 from the
    deep-turn head: [1;1;0;0] when the bit is set, [0;0;0;0] when clear.
    Checked against the tape: v=0 gives the blank wall (s390), v=1 gives
    0,0,1,1 (s586), v=2 gives 0^6,1,1 (s778). *)
Fixpoint slots (bs : list bool) : list Sym :=
  match bs with
  | nil => nil
  | cons true bs' => [1; 1; 0; 0] ++ slots bs'
  | cons false bs' => [0; 0; 0; 0] ++ slots bs'
  end.

Fixpoint bump (bs : list bool) : list bool :=
  match bs with
  | nil => cons true nil
  | cons false bs' => cons true bs'
  | cons true bs' => cons false (bump bs')
  end.

Lemma blank_app : forall n, (const 0 : Stream Sym) = [0]^^n *> const 0.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. apply const_unfold.
Qed.

(** The increment law: a counter has d trailing set bits above a clear one,
    and bumping it clears those d and sets the next. The blank tape
    supplies the clear bit when the stored bits are all set, which is why
    the wall can always grow. *)
Lemma slots_incr : forall bs, exists d bs',
  slots bs *> const 0
    = ([1; 1] ++ [0; 0])^^d *> [0; 0] *> [0; 0] *> slots bs' *> const 0
  /\ slots (bump bs) *> const 0
    = [0]^^(4 * d) *> [1; 1] *> [0; 0] *> slots bs' *> const 0.
Proof.
  induction bs as [| b bs IH].
  - exists O, (@nil bool). simpl. split.
    + exact (blank_app 4).
    + reflexivity.
  - destruct b.
    + destruct IH as [d [bs' [E1 E2]]].
      exists (S d), bs'. split.
      * change (slots (true :: bs)) with ([1; 1; 0; 0] +> slots bs).
        rewrite Str_app_assoc, E1. reflexivity.
      * change (bump (true :: bs)) with (cons false (bump bs)).
        change (slots (false :: bump bs))
          with ([0; 0; 0; 0] +> slots (bump bs)).
        rewrite Str_app_assoc, E2.
        replace (4 * S d) with (4 + 4 * d) by lia.
        rewrite lpow_add, Str_app_assoc. reflexivity.
    + exists O, bs. split.
      * change (slots (false :: bs)) with ([0; 0; 0; 0] +> slots bs).
        rewrite Str_app_assoc. reflexivity.
      * change (bump (false :: bs)) with (cons true bs).
        change (slots (true :: bs)) with ([1; 1; 0; 0] +> slots bs).
        rewrite Str_app_assoc. reflexivity.
Qed.

(** ** CLASS A IS CLOSED.

    From a deep F-turn whose wall is the counter bs in the even alignment,
    the machine reaches the next deep F-turn with the wall the counter
    bumped, one pair fewer on each half, and the block four longer. *)
Lemma classA_step : forall bs k m,
  ([0; 0] *> slots bs *> const 0) <{{F}}
    [0; 1]^^(k + 3) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  ([0; 0] *> slots (bump bs) *> const 0) {{A}}>
    [0; 1]^^(k + 2) *> [0] *> [1]^^(2 * m + 6) *> const 0.
Proof.
  introv.
  destruct (slots_incr bs) as [d [bs' [E1 E2]]].
  rewrite E1.
  change ([0; 0] *> ([1; 1] ++ [0; 0])^^d *> [0; 0] *>
          ([0; 0] *> slots bs' *> const 0))
    with (([0; 0] *> slots bs' *> const 0)
          <* <[0; 0] <* ([1; 1] ++ [0; 0])^^d <* <[0; 0]).
  follow f_to_a.
  rewrite E2.
  replace (4 * d + 2) with (2 + 4 * d) by lia.
  rewrite lpow_add, Str_app_assoc.
  finish.
Qed.

(** ** THE FULL PERIOD (class A).

    Deep A-turn to deep A-turn: the pair count drops by two, the block
    grows by eight, and the wall counter increments by one. Everything
    here is a theorem about the machine, with no side conditions beyond
    the shapes themselves. *)
Theorem full_period : forall bs k m,
  ([0; 0] *> slots bs *> const 0) {{A}}>
    [0; 1]^^(k + 5) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  ([0; 0] *> slots (bump bs) *> const 0) {{A}}>
    [0; 1]^^(k + 3) *> [0] *> [1]^^(2 * m + 10) *> const 0.
Proof.
  introv.
  follow half_period.
  replace (k + 4) with (k + 1 + 3) by lia.
  replace (2 * m + 6) with (2 * (m + 2) + 2) by lia.
  follow classA_step.
  replace (k + 1 + 2) with (k + 3) by lia.
  replace (2 * (m + 2) + 6) with (2 * m + 10) by lia.
  finish.
Qed.

(** ** The era boundary in odometer terms.

    At P = 1 the reset fires and the wall comes back in the ODD alignment
    -- one zero before the counter instead of two -- carrying the bumped
    counter. That shift is real (B1 saw it as the fixed-slot decode
    drifting) and it is what class B below is for. *)
Lemma era_boundary_slots : forall bs M,
  ([0; 0] *> slots bs *> const 0) <{{F}}
    0 >> [1; 0] *> [1]^^(2 * M + 2) *> const 0 -->*
  ([0] *> slots (bump bs) *> const 0) {{A}}>
    [0; 1]^^(M + 3) *> [0] *> [1]^^4 *> const 0.
Proof.
  introv.
  destruct (slots_incr bs) as [d [bs' [E1 E2]]].
  rewrite E1.
  change ([0; 0] *> ([1; 1] ++ [0; 0])^^d *> [0; 0] *>
          ([0; 0] *> slots bs' *> const 0))
    with (([0; 0] *> slots bs' *> const 0)
          <* <[0; 0] <* ([1; 1] ++ [0; 0])^^d <* <[0; 0]).
  follow era_boundary_d.
  rewrite E2.
  replace (4 * d + 1) with (1 + 4 * d) by lia.
  rewrite lpow_add, Str_app_assoc.
  finish.
Qed.

(** ** CLASS B IS CLOSED.

    In the odd alignment the halving eats the counter from the bottom:
    each deep turn consumes one set bit and the pair count goes UP. *)
Lemma classB_step : forall bs2 k m,
  ([0] *> slots (cons true bs2) *> const 0) <{{F}}
    [0; 1]^^(k + 3) *> [0] *> [1]^^(2 * m + 2) *> const 0 -->*
  ([0] *> slots bs2 *> const 0) {{A}}>
    [0; 1]^^(k + 4) *> [0] *> [1]^^(2 * m + 6) *> const 0.
Proof.
  introv.
  change (slots (cons true bs2)) with ([1; 1; 0; 0] +> slots bs2).
  rewrite Str_app_assoc.
  change ([0] *> [1; 1; 0; 0] *> slots bs2 *> const 0)
    with ((slots bs2 *> const 0) <* <[0; 0] <* <[1; 1] <* <[0]).
  follow f_to_a_era.
  finish.
Qed.

(** ** The restructure.

    When the carry chain meets the wall's base run instead of an empty
    slot, the halving runs THROUGH the base: the whole wall is consumed
    and re-emitted as pair material, and the machine arrives at an A-turn
    over blank tape. So a restructure resets the counter to zero -- which
    is why the fixed-slot decode drifts across one (B1's observation),
    and why the invariant only ever has to admit the blank wall here. *)
Lemma f1_to_A_blank : forall r,
  ([1] *> const 0) <{{F}} r -->* (const 0) {{A}}> [0] *> [1] *> r.
Proof. execute. Qed.

Lemma restructure_odd : forall d n r,
  (([1]^^(2 * n + 1) *> const 0) <* ([1; 1] ++ [0; 0])^^d <* <[0; 0]) <{{F}}
    0 >> r -->*
  (const 0) {{A}}> [0] *> [1] *> [0; 1]^^n *> [1]^^(4 * d + 3) *> r.
Proof.
  introv.
  follow excursion_chain.
  rewrite (lpow_add _ (2 * n) 1 [1]), <- lpow_pair, Str_app_assoc.
  follow FA_halve.
  follow f1_to_A_blank.
  finish.
Qed.

(** The even sub-case: the halving consumes the base exactly and the head
    arrives in F over blank tape (F0 = 0LB keeps going left), which is
    what costs the extra rebuild steps B1 measured. Same conclusion for
    the invariant: the counter is reset. *)
Lemma restructure_even : forall d n r,
  (([1]^^(2 * n) *> const 0) <* ([1; 1] ++ [0; 0])^^d <* <[0; 0]) <{{F}}
    0 >> r -->*
  (const 0) <{{F}} [0; 1]^^n *> [1]^^(4 * d + 3) *> r.
Proof.
  introv.
  follow excursion_chain.
  rewrite <- lpow_pair.
  follow FA_halve.
  finish.
Qed.

(** ** The general excursion.

    The census (tools/parity-walllang.mjs) shows 1244 distinct wall shapes
    in 1306 deep turns, so there is no wall grammar to enumerate. What is
    true of EVERY wall is that it is a finite prefix over blank tape, and
    the excursion walks left. Beyond the prefix everything is zero, so the
    no-carry branch must fire: the excursion cannot run forever.

    Base case: over blank tape the excursion is exactly cs_body then the
    bit write. *)
Lemma exc_blank : forall r,
  (const 0) <{{F}} 0 >> r -->*
  ([1; 1] *> const 0) {{C}}> 1 >> 1 >> 1 >> r.
Proof.
  introv.
  rewrite (blank_app 2) at 1.
  follow cs_body.
  rewrite (blank_app 2) at 1.
  follow bitset.
  finish.
Qed.

(** Inductive step: an occupied slot is consumed by the carry and the
    excursion continues two cells deeper, so the finite prefix strictly
    shrinks. This is the termination measure. *)
Lemma exc_carry : forall ws r,
  ((ws *> const 0) <* <[1; 1]) <{{F}} r -->* (ws *> const 0) <{{F}} [0; 1] *> r.
Proof. introv. apply carry_step. Qed.

(** The last atom the dispatcher needs: the bit write when the cell beyond
    the turn already carries a 1. Three steps rather than seven, and it
    lands C on exactly the shape `bitset` does. *)
Lemma bitset_odd : forall l r,
  l <* <[1] <* <[0] <{{F}} 1 >> r -->* l <* <[1; 1] {{C}}> 1 >> r.
Proof. execute. Qed.

(** THE DISPATCHER.

    Only two right-hand phases occur: P0, the head faces `0 1 ..`, and P1,
    it faces `1 ..`. Reading the head cell and the one beyond it gives four
    shapes per phase, and every one of the eight is an atom already proved:

      phase  head,next   atom          effect
      P0     0,0         cs_body       -> P1, two wall cells consumed
      P0     0,1         degen_cs      terminates, F facing right
      P0     1,0         f1_to_A       terminates, A-turn
      P0     1,1         carry_step    -> P0, two wall cells consumed
      P1     0,0         bitset        terminates, C facing right
      P1     0,1         bitset_odd    terminates, C facing right
      P1     1,0         f1_to_A       terminates, A-turn
      P1     1,1         carry_step    -> P0, two wall cells consumed

    So the excursion ends in one of three configurations, whatever the
    wall. *)
Definition ExcOut (c : Q * tape) : Prop :=
  (exists l r, c = l <* <[1; 1] {{C}}> 1 >> r)
  \/ (exists l r, c = l <* <[1; 1] {{F}}> [0; 1] *> r)
  \/ (exists l r, c = l {{A}}> [0] *> [1] *> r).

Lemma exc_blank_1 : forall r,
  exists c, ((const 0 : Stream Sym) <{{F}} 1 >> r) -->* c /\ ExcOut c.
Proof.
  introv.
  exists (((const 0 : Stream Sym) <* <[1; 1]) {{C}}> 1 >> r). split.
  - rewrite (blank_app 2) at 1. follow bitset. finish.
  - left. exists (const 0 : Stream Sym), r. reflexivity.
Qed.

Lemma exc_blank_0 : forall r,
  exists c, ((const 0 : Stream Sym) <{{F}} 0 >> 1 >> r) -->* c /\ ExcOut c.
Proof.
  introv.
  destruct (exc_blank_1 (1 >> 1 >> 1 >> r)) as [c [Hc HO]].
  exists c. split; [| exact HO].
  rewrite (blank_app 2) at 1. follow cs_body. exact Hc.
Qed.

(** Every excursion over every finite wall terminates, in one of the three
    ExcOut shapes. Induction on a bound for the wall's length: the two
    non-terminating branches each eat two cells, and past the end of the
    wall the tape is blank, where the walk is exactly cs_body then the bit
    write. No census, no grammar, no assumption about which walls occur. *)
Lemma excursion_gen : forall n ws r,
  length ws <= n ->
  (exists c, ((ws *> const 0) <{{F}} 0 >> 1 >> r) -->* c /\ ExcOut c)
  /\ (exists c, ((ws *> const 0) <{{F}} 1 >> r) -->* c /\ ExcOut c).
Proof.
  induction n as [| n IH]; introv Hlen.
  - destruct ws as [| a ws].
    + split; [apply exc_blank_0 | apply exc_blank_1].
    + simpl in Hlen. lia.
  - destruct ws as [| a ws].
    { split; [apply exc_blank_0 | apply exc_blank_1]. }
    assert (E : exists b ws',
      (cons a ws) *> const 0 = a >> b >> (ws' *> const 0)
      /\ length ws' <= n).
    { destruct ws as [| b ws'].
      - exists S0, (@nil Sym). split.
        + simpl. rewrite <- const_unfold. reflexivity.
        + simpl. lia.
      - exists b, ws'. split.
        + reflexivity.
        + simpl in Hlen. lia. }
    destruct E as [b [ws' [E Hlen']]].
    rewrite E.
    destruct a; destruct b.
    + split.
      * destruct (IH ws' (1 >> 1 >> 1 >> r) Hlen') as [_ [c [Hc HO]]].
        exists c. split; [| exact HO]. follow cs_body. exact Hc.
      * exists (((ws' *> const 0) <* <[1; 1]) {{C}}> 1 >> r). split.
        { follow bitset. finish. }
        { left. exists (ws' *> const 0), r. reflexivity. }
    + split.
      * exists (((ws' *> const 0) <* <[1; 1]) {{F}}> [0; 1] *> r). split.
        { follow degen_cs. finish. }
        { right. left. exists (ws' *> const 0), r. reflexivity. }
      * exists (((ws' *> const 0) <* <[1; 1]) {{C}}> 1 >> r). split.
        { follow bitset_odd. finish. }
        { left. exists (ws' *> const 0), r. reflexivity. }
    + split.
      * exists ((ws' *> const 0) {{A}}> [0] *> [1] *> 0 >> 1 >> r). split.
        { follow f1_to_A. finish. }
        { right. right. exists (ws' *> const 0), (0 >> 1 >> r). reflexivity. }
      * exists ((ws' *> const 0) {{A}}> [0] *> [1] *> 1 >> r). split.
        { follow f1_to_A. finish. }
        { right. right. exists (ws' *> const 0), (1 >> r). reflexivity. }
    + split.
      * destruct (IH ws' (0 >> 1 >> r) Hlen') as [[c [Hc HO]] _].
        exists c. split; [| exact HO]. follow carry_step.
        cbn [Str_app]. exact Hc.
      * destruct (IH ws' (1 >> r) Hlen') as [[c [Hc HO]] _].
        exists c. split; [| exact HO]. follow carry_step.
        cbn [Str_app]. exact Hc.
Qed.

(** The excursion, stated the way the rest of the proof consumes it: from
    ANY deep F-turn -- any finite wall, any right-hand tail -- the machine
    reaches one of three shapes. *)
Corollary excursion : forall ws r,
  exists c, ((ws *> const 0) <{{F}} 0 >> 1 >> r) -->* c /\ ExcOut c.
Proof.
  introv. apply (excursion_gen (length ws) ws r). lia.
Qed.

(** ** THE RUN-LEVEL MACRO STEP.

    Stripped of all context the machine is a four-phase cycle: B scans right
    over 1s to the first 0 and writes it, C scans right over the NEXT 1-run
    and erases it, D/E fill that zero field leftward, F/A halve leftward
    over 1s. Only the fill can halt, and only by reading a 1 in state E.

    Counting the fill's alternation gives the halt criterion outright. Let
    the tape from B's entry read `1^a 0^b 1^c 0^d ..`. The fill starts one
    cell past the 0 that C stopped on, so it reads a 1 immediately when
    d = 1 (safe, whatever c is), and otherwise crosses c + 2 cells before
    meeting the 1 that B wrote -- safe iff c is EVEN. So:

      the machine halts iff some C-scan erases an ODD run of 1s that is
      followed by a zero-run of length two or more.

    Both branches are proved below, for arbitrary a, c, n and arbitrary
    context on both sides. macro_fill generalises punch_refill, which
    needed blank tape past the block. *)

Lemma macro_fill : forall a n l r,
  l {{B}}> [1]^^a *> [0] *> [1]^^(2 * n) *> [0; 0] *> r -->*
  l <* <[1]^^a <{{F}} [1]^^(2 * n + 3) *> r.
Proof.
  introv.
  follow B_phase.
  follow C_phase.
  execute.
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (n + n) with (2 * n) by lia.
  rewrite <- lpow_pair.
  follow DE_fill.
  execute.
  rewrite <- ones_comm, lpow_pair.
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (n + n) with (2 * n) by lia.
  finish.
Qed.

(** The gap-zero branch: a single 0 after the erased run, so the fill reads
    its 1 at once and the run's parity is irrelevant. This is why the pair
    region is safe at every length -- its zero-runs are all singletons. *)
Lemma macro_gap0 : forall a c l r,
  l {{B}}> [1]^^a *> [0] *> [1]^^c *> [0] *> 1 >> r -->*
  l <* <[1]^^(a + 1) <* <[0]^^(c + 1) <{{F}} 1 >> r.
Proof.
  introv.
  follow B_phase.
  follow C_phase.
  execute.
Qed.

(** ** Startup: c0 to the first structured configuration. *)

Lemma startup : c0 -->* const 0 <* <[1] {{B}}> [1; 1; 1; 1] *> const 0.
Proof. execute. Qed.

(** ** THE RUN-LEVEL MACHINE.

    tools/parity-macro.mjs implements the machine at this granularity and
    is co-verified against the raw simulator at every one of 2,498,992
    fill exits over 2e7 steps, byte-exact. The right side is a list of
    1-run lengths separated by single zeros over blank; a cap bit marks a
    leading zero (the P0 form). The wall is a raw cell list over blank.

    `exc` computes the excursion's exit -- which of C or B re-enters the
    right side, with what wall and what right word -- from any wall at
    all. `exc_sim` below proves it: the run-level machine IS the machine. *)

Fixpoint runs (rs : list nat) : Stream Sym :=
  match rs with
  | nil => const 0
  | cons r rest => [1]^^r *> 0 >> runs rest
  end.

Definition rside (cap : bool) (rs : list nat) : Stream Sym :=
  if cap then 0 >> runs rs else runs rs.

Definition rhead (rs : list nat) : nat :=
  match rs with nil => O | cons r _ => r end.

(** The push algebra: what each excursion move does to the right word.
    A carry prepends `0 1`; the A0 turn and the B-scan entry prepend a
    bare 1; the CS body eats the cap and prepends three 1s. *)
Definition cpush (cap : bool) (rs : list nat) : list nat :=
  if cap then cons (S O) rs
  else match rs with
       | nil => cons (S O) nil
       | cons r rest => cons (S r) rest
       end.

Definition push3 (rs : list nat) : list nat :=
  match rs with
  | nil => cons (S (S (S O))) nil
  | cons r rest => cons (S (S (S r))) rest
  end.

Lemma ones_S : forall n (X : Stream Sym), [1]^^(S n) *> X = 1 >> [1]^^n *> X.
Proof. reflexivity. Qed.

Lemma runs_cons : forall r rest, runs (cons r rest) = [1]^^r *> 0 >> runs rest.
Proof. reflexivity. Qed.

Lemma runs_expose : forall r rest,
  runs (cons (S r) rest) = 1 >> [1]^^r *> 0 >> runs rest.
Proof. introv. cbn [runs]. apply ones_S. Qed.

Lemma cpush_eq : forall cap rs, [0; 1] *> rside cap rs = rside true (cpush cap rs).
Proof.
  introv. destruct cap.
  - reflexivity.
  - destruct rs as [| r rest].
    + cbn [rside cpush runs]. rewrite (blank_app 1) at 1. reflexivity.
    + reflexivity.
Qed.

Lemma push1_eq : forall cap rs, 1 >> rside cap rs = runs (cpush cap rs).
Proof.
  introv. destruct cap.
  - reflexivity.
  - destruct rs as [| r rest].
    + cbn [rside cpush runs]. rewrite (blank_app 1) at 1. reflexivity.
    + reflexivity.
Qed.

Lemma push3_eq : forall rs, 1 >> 1 >> 1 >> runs rs = runs (push3 rs).
Proof.
  introv. destruct rs as [| r rest].
  - cbn [push3 runs]. rewrite (blank_app 1) at 1. reflexivity.
  - reflexivity.
Qed.

Lemma cpush_pos : forall cap rs, 1 <= rhead (cpush cap rs).
Proof. introv. destruct cap; cbn; [lia |]. destruct rs; cbn; lia. Qed.

Lemma push3_pos : forall rs, 1 <= rhead (push3 rs).
Proof. introv. destruct rs; cbn; lia. Qed.

(** The degenerate CS body composed through to the C-entry (degen_cs plus
    the three-step F0/B1/B0 turn). *)
Lemma degen_full : forall l r,
  l <* <[1] <* <[0] <{{F}} 0 >> 1 >> r -->* l <* <[1; 1; 1] {{C}}> 1 >> r.
Proof. execute. Qed.

Lemma a0_step : forall l r, l {{A}}> 0 >> r -->* l <* <[1] {{B}}> r.
Proof. execute. Qed.

(** The excursion, as a function. Exits: ExC = C re-enters (erasing the
    leading run), ExB = B re-enters (skimming it). Two wall cells per
    move; the exits push their bit-write 1s back onto the wall. *)
Inductive xexit : Type :=
  | ExC : list Sym -> list nat -> xexit
  | ExB : list Sym -> list nat -> xexit.

Fixpoint exc (ws : list Sym) (cap : bool) (rs : list nat) : xexit :=
  match ws with
  | cons 1 (cons 1 ws') => exc ws' true (cpush cap rs)
  | cons 1 (cons 0 ws') => ExB (cons 1 ws') (cpush cap rs)
  | cons 1 nil => ExB (cons 1 nil) (cpush cap rs)
  | cons 0 (cons 0 ws') =>
      if cap then exc ws' false (push3 rs) else ExC (cons 1 (cons 1 ws')) rs
  | cons 0 (cons 1 ws') =>
      ExC (if cap then cons 1 (cons 1 (cons 1 ws')) else cons 1 (cons 1 ws')) rs
  | cons 0 nil =>
      if cap then ExC (cons 1 (cons 1 nil)) (push3 rs)
      else ExC (cons 1 (cons 1 nil)) rs
  | nil =>
      if cap then ExC (cons 1 (cons 1 nil)) (push3 rs)
      else ExC (cons 1 (cons 1 nil)) rs
  end.

Definition xconf (x : xexit) : Q * tape :=
  match x with
  | ExC ws rs => (ws *> const 0) {{C}}> runs rs
  | ExB ws rs => (ws *> const 0) {{B}}> runs rs
  end.

Lemma zpad : 0 >> (const 0 : Stream Sym) = const 0.
Proof. symmetry. apply const_unfold. Qed.

(** The excursion exits as strict progress: each has a concrete head cell,
    so one peeled step turns the rest over to the evstep machinery. These
    carry the `-->+` that progress_nonhalt needs through the whole proof. *)
Lemma bitset_plus : forall l r,
  l <* <[0; 0] <{{F}} 1 >> r -->+ l <* <[1; 1] {{C}}> 1 >> r.
Proof. introv. start_progress. Qed.

Lemma bitset_odd_plus : forall l r,
  l <* <[1] <* <[0] <{{F}} 1 >> r -->+ l <* <[1; 1] {{C}}> 1 >> r.
Proof. introv. start_progress. Qed.

Lemma degen_full_plus : forall l r,
  l <* <[1] <* <[0] <{{F}} 0 >> 1 >> r -->+ l <* <[1; 1; 1] {{C}}> 1 >> r.
Proof. introv. start_progress. Qed.

Lemma f1_to_A_plus : forall l r,
  l <* <[0] <* <[1] <{{F}} r -->+ l {{A}}> [0] *> [1] *> r.
Proof. introv. start_progress. Qed.

(** The blank-wall excursion: the CS body fires over blank cells (when
    capped) and the bit write ends it. *)
Lemma exc_blank_sim : forall cap rs,
  1 <= rhead rs ->
  (const 0 : Stream Sym) <{{F}} rside cap rs -->+ xconf (exc nil cap rs).
Proof.
  introv Hrs.
  destruct cap; cbn [exc xconf rside].
  - rewrite (blank_app 2) at 1.
    follow cs_body.
    rewrite (blank_app 2) at 1.
    eapply progress_evstep_trans; [apply bitset_plus |].
    rewrite push3_eq. finish.
  - destruct rs as [| r rest]; [cbn in Hrs; lia |].
    destruct r as [| r]; [cbn in Hrs; lia |].
    rewrite runs_expose.
    rewrite (blank_app 2) at 1.
    eapply progress_evstep_trans; [apply bitset_plus |].
    rewrite <- runs_expose. finish.
Qed.

(** THE SIMULATION. From any deep turn -- any finite wall, any right word
    with a positive leading run -- the machine runs the excursion and
    arrives exactly where `exc` says, with the exact wall and word. This
    strengthens excursion_gen from an existential to a computation. *)
Lemma exc_sim : forall n ws cap rs,
  length ws <= n ->
  1 <= rhead rs ->
  (ws *> const 0) <{{F}} rside cap rs -->+ xconf (exc ws cap rs).
Proof.
  induction n as [| n IH]; introv Hlen Hrs.
  - destruct ws; [| cbn in Hlen; lia ].
    apply exc_blank_sim, Hrs.
  - destruct ws as [| a ws].
    { apply exc_blank_sim, Hrs. }
    destruct ws as [| b ws].
    + (* singleton wall: pad the stream with one blank cell *)
      destruct a; cbn [exc].
      * (* a = 0: the bitset family at the blank edge *)
        assert (P : (cons 0 nil) *> const 0
                    = (const 0 : Stream Sym) <* <[0; 0]).
        { cbn [Str_app]. f_equal. apply const_unfold. }
        rewrite P.
        destruct cap; cbn [xconf rside].
        -- follow cs_body.
           rewrite (blank_app 2) at 1.
           eapply progress_evstep_trans; [apply bitset_plus |].
           rewrite push3_eq. finish.
        -- destruct rs as [| r rest]; [cbn in Hrs; lia |].
           destruct r as [| r]; [cbn in Hrs; lia |].
           rewrite runs_expose.
           eapply progress_evstep_trans; [apply bitset_plus |].
           rewrite <- runs_expose. finish.
      * (* a = 1: f1_to_A at the blank edge *)
        assert (P : (cons 1 nil) *> const 0
                    = (const 0 : Stream Sym) <* <[0] <* <[1]).
        { cbn [Str_app]. f_equal. apply const_unfold. }
        rewrite P.
        cbn [exc xconf].
        eapply progress_evstep_trans; [apply f1_to_A_plus |].
        follow a0_step.
        cbn [Str_app].
        rewrite push1_eq.
        finish.
    + (* two explicit cells *)
      cbn in Hlen.
      assert (Hlen' : length ws <= n) by lia.
      destruct a; destruct b; cbn [exc].
      * (* 0,0 *)
        change ((0 :: 0 :: ws) *> const 0)
          with ((ws *> const 0) <* <[0; 0]).
        destruct cap; cbn [xconf rside].
        -- follow cs_body.
           rewrite push3_eq.
           apply (IH ws false (push3 rs) Hlen' (push3_pos rs)).
        -- destruct rs as [| r rest]; [cbn in Hrs; lia |].
           destruct r as [| r]; [cbn in Hrs; lia |].
           rewrite runs_expose.
           eapply progress_evstep_trans; [apply bitset_plus |].
           rewrite <- runs_expose. finish.
      * (* 0,1 *)
        change ((0 :: 1 :: ws) *> const 0)
          with ((ws *> const 0) <* <[1] <* <[0]).
        destruct rs as [| r rest]; [cbn in Hrs; lia |].
        destruct r as [| r]; [cbn in Hrs; lia |].
        destruct cap; cbn [xconf rside].
        -- rewrite runs_expose.
           eapply progress_evstep_trans; [apply degen_full_plus |].
           rewrite <- runs_expose. finish.
        -- rewrite runs_expose.
           eapply progress_evstep_trans; [apply bitset_odd_plus |].
           rewrite <- runs_expose. finish.
      * (* 1,0 *)
        change ((1 :: 0 :: ws) *> const 0)
          with ((ws *> const 0) <* <[0] <* <[1]).
        cbn [xconf].
        eapply progress_evstep_trans; [apply f1_to_A_plus |].
        follow a0_step.
        cbn [Str_app].
        rewrite push1_eq.
        finish.
      * (* 1,1: the carry *)
        change ((1 :: 1 :: ws) *> const 0)
          with ((ws *> const 0) <* <[1; 1]).
        follow carry_step.
        rewrite cpush_eq.
        apply (IH ws true (cpush cap rs) Hlen' (cpush_pos cap rs)).
Qed.

(** ** The macro step: from a C- or B-entry to the next one.

    Every excursion exit funnels into a C-entry (erase the leading run) or
    a B-entry (skim it). One entry plus one excursion is `mstep`; the None
    cases are exactly the halt criterion (an odd run erased at the right
    edge) and shapes the invariant will exclude. *)

Inductive mst : Type :=
  | MC : list Sym -> list nat -> mst
  | MB : list Sym -> list nat -> mst.

Definition mconf (s : mst) : Q * tape :=
  match s with
  | MC ws rs => (ws *> const 0) {{C}}> runs rs
  | MB ws rs => (ws *> const 0) {{B}}> runs rs
  end.

Definition mrs (s : mst) : list nat :=
  match s with MC _ rs => rs | MB _ rs => rs end.

Definition of_exit (x : xexit) : mst :=
  match x with ExC ws rs => MC ws rs | ExB ws rs => MB ws rs end.

Lemma xconf_of_exit : forall x, mconf (of_exit x) = xconf x.
Proof. destruct x; reflexivity. Qed.

Definition mstep (s : mst) : option mst :=
  match s with
  | MB ws nil => None
  | MB ws (cons a rest) => Some (MC ([1]^^(S a) ++ ws) rest)
  | MC ws nil =>
      match ws with
      | cons 1 ws' => Some (of_exit (exc ws' false (cons 3 nil)))
      | _ => None
      end
  | MC ws (cons c nil) =>
      if Nat.even c
      then match ws with
           | cons 1 ws' => Some (of_exit (exc ws' false (cons (3 + c) nil)))
           | _ => None
           end
      else None
  | MC ws (cons c rest) => Some (of_exit (exc ([0]^^(S c) ++ ws) false rest))
  end.

(** The B-scan entry: skim the leading run, convert the separator, hand C
    the rest. Uniform over `rest` (the separator comes from blank when the
    run is last). *)
Lemma be_sim : forall a rest ws,
  (ws *> const 0) {{B}}> runs (cons a rest) -->+
  (([1]^^(S a) ++ ws) *> const 0) {{C}}> runs rest.
Proof.
  introv. rewrite Str_app_assoc. cbn [runs].
  follow B_ones. execute.
Qed.

(** The C-scan entry, gap-0 branch: the erased run and its separator turn
    to wall zeros, the fill reads a 1 at once, and the run's parity never
    matters. This is the nibble that keeps the machine safe in the pair
    region. *)
Lemma ce_gap0_sim : forall c r rest ws,
  (ws *> const 0) {{C}}> runs (cons c (cons (S r) rest)) -->*
  (([0]^^(S c) ++ ws) *> const 0) <{{F}} runs (cons (S r) rest).
Proof.
  introv. rewrite Str_app_assoc. cbn [runs].
  follow C_ones. execute.
Qed.

(** The C-scan entry at the right edge, empty word: the c = 0 fill. *)
Lemma ce_edge_sim : forall ws,
  ((cons 1 ws) *> const 0) {{C}}> runs nil -->*
  (ws *> const 0) <{{F}} runs (cons 3 nil).
Proof.
  introv. cbn [runs]. rewrite zpad. execute.
Qed.

(** The C-scan entry at the right edge, the punch: the whole (even) run is
    erased, the fill crosses the even gap -- the halt criterion, satisfied
    -- and the wall's top 1 is drawn into the refilled run. *)
Lemma ce_fill_sim : forall n ws,
  ((cons 1 ws) *> const 0) {{C}}> runs (cons (2 * n) nil) -->*
  (ws *> const 0) <{{F}} runs (cons (3 + 2 * n) nil).
Proof.
  introv.
  assert (E2 : runs (cons (2 * n) nil) = [1]^^(2 * n) *> const 0).
  { cbn [runs]. rewrite zpad. reflexivity. }
  assert (E : runs (cons (3 + 2 * n) nil)
              = 1 >> 1 >> [1; 1]^^n *> 1 >> const 0).
  { cbn [runs]. rewrite zpad.
    replace (3 + 2 * n) with (2 + (2 * n + 1)) by lia.
    rewrite lpow_add, Str_app_assoc.
    rewrite (lpow_add _ (2 * n) 1), Str_app_assoc.
    rewrite <- lpow_pair.
    reflexivity. }
  rewrite E2, E.
  change ((cons 1 ws) *> const 0) with ((ws *> const 0) <* <[1]).
  follow C_ones.
  execute.
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (n + n) with (2 * n) by lia.
  rewrite <- lpow_pair.
  follow DE_fill.
  execute.
  rewrite ones_comm.
  finish.
Qed.

(** THE MACRO STEP SIMULATES. One entry plus one excursion, composed. *)
Lemma mstep_sim : forall s s',
  List.Forall (le 1) (mrs s) ->
  mstep s = Some s' ->
  mconf s -->+ mconf s'.
Proof.
  introv Hwf Hstep. destruct s as [ws rs | ws rs].
  - destruct rs as [| c rest].
    + (* right edge, empty word: the c = 0 fill *)
      destruct ws as [| a ws']; [discriminate |].
      destruct a; [discriminate |].
      inversion Hstep; subst s'; clear Hstep.
      eapply evstep_progress_trans; [apply ce_edge_sim |].
      rewrite xconf_of_exit.
      apply (exc_sim (length ws') ws' false (cons 3 nil));
        [constructor | cbn; lia].
    + destruct rest as [| r2 rest'].
      * (* right edge, the punch *)
        cbn [mstep] in Hstep.
        destruct (Nat.even c) eqn:Ec; [| discriminate].
        destruct ws as [| a ws']; [discriminate |].
        destruct a; [discriminate |].
        inversion Hstep; subst s'; clear Hstep.
        apply Nat.even_spec in Ec. destruct Ec as [n En]. subst c.
        eapply evstep_progress_trans; [apply ce_fill_sim |].
        rewrite xconf_of_exit.
        apply (exc_sim (length ws') ws' false (cons (3 + 2 * n) nil));
          [constructor | cbn; lia].
      * (* the gap-0 nibble *)
        cbn [mstep] in Hstep.
        inversion Hstep; subst s'; clear Hstep.
        inversion Hwf as [| ? ? H1 Hwf1]; subst.
        inversion Hwf1 as [| ? ? H2 Hwf2]; subst.
        destruct r2 as [| r2]; [lia |].
        eapply evstep_progress_trans; [apply ce_gap0_sim |].
        rewrite xconf_of_exit.
        apply (exc_sim (length ([0]^^(S c) ++ ws)) ([0]^^(S c) ++ ws)
                 false (cons (S r2) rest')); [constructor | cbn; lia].
  - destruct rs as [| a rest]; [discriminate |].
    cbn [mstep] in Hstep.
    inversion Hstep; subst s'; clear Hstep.
    apply be_sim.
Qed.

(** ** Nibble preservation.

    A right word with at least two runs is protected: every C-erasure
    inside it stops at a single 0 (gap 0), and the excursion's pushes only
    prepend or grow the head run, so the run count never drops, every run
    stays positive, and the LAST run -- the only one a fill can ever
    erase -- is untouched. This is the reason the machine is safe in the
    pair region whatever the wall looks like. *)

Definition nib (rs : list nat) : Prop :=
  2 <= length rs /\ List.Forall (le 1) rs /\ Nat.even (List.last rs O) = true.

Lemma last_cons : forall (x : nat) l d, l <> nil -> List.last (cons x l) d = List.last l d.
Proof. introv H. destruct l; [contradiction | reflexivity]. Qed.

Lemma nib_cpush : forall cap rs, nib rs -> nib (cpush cap rs).
Proof.
  introv [Hlen [Hpos Hlast]].
  destruct cap; cbn [cpush].
  - split; [cbn; lia |]. split.
    + constructor; [lia | exact Hpos].
    + rewrite last_cons; [exact Hlast |].
      destruct rs; [cbn in Hlen; lia | discriminate].
  - destruct rs as [| r rest]; [cbn in Hlen; lia |].
    destruct rest as [| r2 rest]; [cbn in Hlen; lia |].
    split; [cbn; cbn in Hlen; lia |]. split.
    + inversion Hpos; subst. constructor; [lia | assumption].
    + rewrite last_cons in *; try discriminate. exact Hlast.
Qed.

Lemma nib_push3 : forall rs, nib rs -> nib (push3 rs).
Proof.
  introv [Hlen [Hpos Hlast]].
  destruct rs as [| r rest]; [cbn in Hlen; lia |].
  destruct rest as [| r2 rest]; [cbn in Hlen; lia |].
  cbn [push3]. split; [cbn; cbn in Hlen; lia |]. split.
  - inversion Hpos; subst. constructor; [lia | assumption].
  - rewrite last_cons in *; try discriminate. exact Hlast.
Qed.

(** Through any excursion over any wall: a nibble word exits as a nibble
    word, and the exit wall starts with the bit write's 1s. *)
Lemma exc_nib : forall n ws cap rs,
  length ws <= n ->
  nib rs ->
  match exc ws cap rs with
  | ExC ws' rs' => nib rs' /\ exists t, ws' = cons 1 (cons 1 t)
  | ExB ws' rs' => nib rs' /\ exists t, ws' = cons 1 t
  end.
Proof.
  induction n as [| n IH]; introv Hlen Hnib.
  - destruct ws; [| cbn in Hlen; lia ].
    cbn [exc]. destruct cap.
    + split; [apply nib_push3, Hnib | eauto].
    + split; [exact Hnib | eauto].
  - destruct ws as [| a ws].
    { cbn [exc]. destruct cap.
      + split; [apply nib_push3, Hnib | eauto].
      + split; [exact Hnib | eauto]. }
    destruct ws as [| b ws].
    + destruct a; cbn [exc].
      * destruct cap.
        -- split; [apply nib_push3, Hnib | eauto].
        -- split; [exact Hnib | eauto].
      * split; [apply nib_cpush, Hnib | eauto].
    + cbn in Hlen.
      assert (Hlen' : length ws <= n) by lia.
      destruct a; destruct b; cbn [exc].
      * destruct cap.
        -- exact (IH ws false (push3 rs) Hlen' (nib_push3 rs Hnib)).
        -- split; [exact Hnib | eauto].
      * destruct cap.
        -- split; [exact Hnib | eauto].
        -- split; [exact Hnib | eauto].
      * split; [apply nib_cpush, Hnib | eauto].
      * exact (IH ws true (cpush cap rs) Hlen' (nib_cpush cap rs Hnib)).
Qed.

(** ** The excursion at its call sites, computed.

    mstep only ever invokes exc from two wall shapes: a zero-topped wall
    (after a gap-0 nibble: immediate bit-write exit) and a one-run-topped
    wall (after a fill: the carries resolve it). These equations and the
    absorb/insulate resolutions below compute every case. *)

Lemma exc_zz : forall ws cap rs,
  exc (cons 0 (cons 0 ws)) cap rs
  = if cap then exc ws false (push3 rs) else ExC (cons 1 (cons 1 ws)) rs.
Proof. reflexivity. Qed.

(** Prepending j ones to the word: what j capped carries do. *)
Fixpoint prep (j : nat) (rs : list nat) : list nat :=
  match j with O => rs | S j' => cons (S O) (prep j' rs) end.

Lemma prep_comm : forall j rs, prep j (cons (S O) rs) = cons (S O) (prep j rs).
Proof.
  induction j; introv; cbn [prep].
  - reflexivity.
  - rewrite IHj. reflexivity.
Qed.

(** A run of 2j ones under a capped word: j carries, each prepending 1. *)
Lemma exc_run_t : forall j wt rs,
  exc ([1]^^(2 * j) ++ wt) true rs = exc wt true (prep j rs).
Proof.
  induction j; introv.
  - reflexivity.
  - replace (2 * S j) with (S (S (2 * j))) by lia.
    cbn [lpow]. rewrite <- List.app_assoc. cbn [List.app].
    change (exc (cons 1 (cons 1 ([1]^^(2 * j) ++ wt))) true rs)
      with (exc ([1]^^(2 * j) ++ wt) true (cpush true rs)).
    rewrite IHj.
    change (cpush true rs) with (cons (S O) rs).
    rewrite prep_comm. reflexivity.
Qed.

(** A capped odd run over a zero: the carries prepend and the last cell
    meets (1,0) -- the A0 turn hands B the word. *)
Lemma exc_odd_t : forall j wt rs,
  exc ([1]^^(2 * j + 1) ++ cons 0 wt) true rs
  = ExB (cons 1 wt) (cons (S O) (prep j rs)).
Proof.
  induction j; introv.
  - reflexivity.
  - replace (2 * S j + 1) with (S (S (2 * j + 1))) by lia.
    cbn [lpow]. rewrite <- List.app_assoc. cbn [List.app].
    change (exc (cons 1 (cons 1 ([1]^^(2 * j + 1) ++ cons 0 wt))) true rs)
      with (exc ([1]^^(2 * j + 1) ++ cons 0 wt) true (cpush true rs)).
    rewrite IHj.
    change (cpush true rs) with (cons (S O) rs).
    rewrite prep_comm. reflexivity.
Qed.

Lemma exc_odd_t_nil : forall j rs,
  exc ([1]^^(2 * j + 1)) true rs
  = ExB (cons 1 nil) (cons (S O) (prep j rs)).
Proof.
  induction j; introv.
  - reflexivity.
  - replace (2 * S j + 1) with (S (S (2 * j + 1))) by lia.
    cbn [lpow].
    change (exc ([1] ++ [1] ++ [1]^^(2 * j + 1)) true rs)
      with (exc ([1]^^(2 * j + 1)) true (cpush true rs)).
    rewrite IHj.
    change (cpush true rs) with (cons (S O) rs).
    rewrite prep_comm. reflexivity.
Qed.

(** The absorb resolution: an odd run of usable ones over a zero (or the
    blank edge). The run is folded into the wall and B relaunches. *)
Lemma exc_absorb : forall j x wt,
  exc ([1]^^(2 * j + 1) ++ cons 0 wt) false (cons x nil)
  = ExB (cons 1 wt) (prep j (cons (S x) nil)).
Proof.
  destruct j; introv.
  - reflexivity.
  - replace (2 * S j + 1) with (S (S (2 * j + 1))) by lia.
    cbn [lpow]. rewrite <- List.app_assoc. cbn [List.app].
    change (exc (cons 1 (cons 1 ([1]^^(2 * j + 1) ++ cons 0 wt))) false (cons x nil))
      with (exc ([1]^^(2 * j + 1) ++ cons 0 wt) true (cons (S x) nil)).
    rewrite exc_odd_t. reflexivity.
Qed.

Lemma exc_absorb_nil : forall j x,
  exc ([1]^^(2 * j + 1)) false (cons x nil)
  = ExB (cons 1 nil) (prep j (cons (S x) nil)).
Proof.
  destruct j; introv.
  - reflexivity.
  - replace (2 * S j + 1) with (S (S (2 * j + 1))) by lia.
    cbn [lpow].
    change (exc ([1] ++ [1] ++ [1]^^(2 * j + 1)) false (cons x nil))
      with (exc ([1]^^(2 * j + 1)) true (cons (S x) nil)).
    rewrite exc_odd_t_nil. reflexivity.
Qed.

(** The insulate resolution, first stage: an even run >= 4 spends two
    carries turning the exposed run into the two-run capped word
    [1, x+1] -- the block is even and behind a single gap from here on,
    and the rest of the excursion is nibble-protected. *)
Lemma exc_insulate : forall j x wt,
  exc ([1]^^(2 * j + 4) ++ wt) false (cons x nil)
  = exc ([1]^^(2 * j) ++ wt) true (cons (S O) (cons (S x) nil)).
Proof.
  introv.
  replace (2 * j + 4) with (S (S (S (S (2 * j))))) by lia.
  cbn [lpow]. rewrite <- !List.app_assoc. cbn [List.app].
  reflexivity.
Qed.

(** ** The word-suffix guard.

    w3 forbids the one dangerous suffix: a run >= 2, then a single pair
    run, then the final block. Its gap-0 would hand C the [1, L] word
    over a wall-top of exactly 2, whose c = 1 nibble punches the block
    at usable-top 3 -- the dead class. Everything the machine ever
    pushes or consumes preserves w3; checked at 15M C/B-entries. *)
Fixpoint w3 (rs : list nat) : Prop :=
  match rs with
  | cons a (cons b (cons c nil)) => 2 <= a -> b <> S O
  | cons _ rest => w3 rest
  | nil => True
  end.

Lemma w3_tail : forall a rest, w3 (cons a rest) -> w3 rest.
Proof.
  introv H.
  destruct rest as [| b rest]; [exact I |].
  destruct rest as [| c rest]; [exact I |].
  destruct rest as [| d rest]; [exact I | exact H].
Qed.

Lemma w3_cons1 : forall rs, w3 rs -> w3 (cons (S O) rs).
Proof.
  introv H.
  destruct rs as [| b rest]; [exact I |].
  destruct rest as [| c rest]; [exact I |].
  destruct rest as [| d rest]; [| exact H].
  cbn. intro Habs. lia.
Qed.

(** Head merges (the carry's +1, the CS body's +3) preserve w3 whenever
    the old head was already >= 2 -- which the excursion guarantees at
    every merge site after the initial run. *)
Lemma w3_head_ge : forall a a' rest,
  2 <= a -> w3 (cons a rest) -> w3 (cons a' rest).
Proof.
  introv Ha H.
  destruct rest as [| b rest]; [exact I |].
  destruct rest as [| c rest]; [exact I |].
  destruct rest as [| d rest]; [| exact H].
  cbn in *. intro. apply H, Ha.
Qed.

(** ** THE INVARIANT.

    Validated against the abstract machine at 15,005,277 consecutive
    C-/B-entries (30M events): every clause below holds at every one.
    fillok is the fill-time law: the usable top-run u = wallT - 1 of a
    punch avoids 0 (exposed exit), 2 (one carry then cs re-exposes),
    3 (absorb hands MB [1,c+4], whose skim punches at u = 2) and 6 (the
    insulate cs collides with the [1,1,L] transient). wallok: interior
    wall 1-runs are never singletons (only the f1A turn writes a lone 1,
    always at the top, and the next skim merges it). *)

Fixpoint wallT (ws : list Sym) : nat :=
  match ws with cons 1 t => S (wallT t) | _ => O end.

Fixpoint zrun (ws : list Sym) : nat :=
  match ws with cons 0 t => S (zrun t) | _ => O end.

Definition wgap (ws : list Sym) : nat := zrun (List.skipn (wallT ws) ws).

Definition fillok (u : nat) : Prop :=
  u = S O \/ u = 4 \/ u = 5 \/ 7 <= u.

Fixpoint wallok (ws : list Sym) : Prop :=
  match ws with
  | cons 0 (cons 1 (cons 0 _)) => False
  | cons 0 (cons 1 nil) => False
  | cons _ t => wallok t
  | nil => True
  end.

Definition Inv (s : mst) : Prop :=
  match s with
  | MC ws rs =>
      2 <= wallT ws /\ wallok ws /\ List.Forall (le 1) rs /\
      match rs with
      | nil => fillok (wallT ws - S O) /\ (wallT ws = 5 -> wgap ws <> S O)
      | cons c nil => Nat.even c = true /\ fillok (wallT ws - S O)
                      /\ (wallT ws = 5 -> wgap ws <> S O)
      | cons c rest =>
          Nat.even (List.last rs O) = true /\ w3 rs /\
          (forall r2, rs = cons (S O) (cons r2 nil) ->
             wallT ws = 3 \/ wallT ws = 4 \/ 7 <= wallT ws)
      end
  | MB ws rs =>
      1 <= wallT ws /\ wallok ws /\ List.Forall (le 1) rs /\
      match rs with
      | nil => False
      | cons a nil => 4 <= a /\ Nat.even a = true
      | cons a (cons _ nil) => False
      | cons a rest =>
          Nat.even (List.last rs O) = true /\ w3 rs /\ a = S O
      end
  end.

(** The safety half of closure: an invariant state always has a
    successor -- mstep's None branches are unreachable. The other half
    (Inv is preserved) is the remaining work. *)
Lemma inv_safe : forall s, Inv s -> exists s', mstep s = Some s'.
Proof.
  introv HI. destruct s as [ws rs | ws rs]; cbn in HI.
  - destruct HI as [HT [Hok [Hwf Hrs]]].
    destruct ws as [| a ws']; [cbn in HT; lia |].
    destruct a; [cbn in HT; lia |].
    destruct rs as [| c rest].
    + eexists. reflexivity.
    + destruct rest as [| r2 rest'].
      * destruct Hrs as [Hc _]. cbn [mstep]. rewrite Hc. eexists. reflexivity.
      * eexists. reflexivity.
  - destruct HI as [HT [Hok [Hwf Hrs]]].
    destruct rs as [| a rest]; [contradiction |].
    eexists. reflexivity.
Qed.

(** ** The deep excursion.

    Entered only after the first CS body of an insulate resolution. From
    there every uncapped head is >= 2 (the CS merge put it there), capped
    two-run words keep heads >= 2, and the one dangerous capped shape
    [1, b, y] always carries b >= 2. wallok rules out interior singleton
    1-runs, so an uncapped state never faces (1,0): deep f1A is always
    post-carry, a prepend, never a merge. *)

Definition second (rs : list nat) : nat :=
  match rs with cons _ (cons b _) => b | _ => O end.

Lemma wallok_tail : forall a ws, wallok (cons a ws) -> wallok ws.
Proof.
  introv H.
  destruct a.
  - destruct ws as [| b ws]; [exact I |].
    destruct b; [exact H |].
    destruct ws as [| c ws]; [contradiction |].
    destruct c; [contradiction | exact H].
  - exact H.
Qed.

Lemma wallok_zero_guard : forall ws,
  wallok (cons 0 ws) ->
  (forall t, ws <> cons 1 (cons 0 t)) /\ ws <> cons 1 nil.
Proof.
  introv H. split.
  - introv E. subst ws. contradiction.
  - introv E. subst ws. contradiction.
Qed.

Definition dmot (ws : list Sym) (cap : bool) (rs : list nat) : Prop :=
  nib rs /\ w3 rs /\ wallok ws /\
  (cap = false -> 2 <= rhead rs /\
     (forall t, ws <> cons 1 (cons 0 t)) /\ ws <> cons 1 nil) /\
  (cap = true ->
     (length rs = 2 -> 2 <= rhead rs) /\
     (length rs = 3 -> rhead rs = S O -> 2 <= second rs)).

(** push3 under the capped conditions keeps w3. *)
Lemma w3_push3_cap : forall rs,
  nib rs -> w3 rs ->
  (length rs = 2 -> 2 <= rhead rs) ->
  (length rs = 3 -> rhead rs = S O -> 2 <= second rs) ->
  w3 (push3 rs).
Proof.
  introv Hnib Hw3 H2 H3.
  destruct rs as [| a rest]; [exact I |].
  cbn [push3].
  destruct rest as [| b rest]; [exact I |].
  destruct rest as [| c rest]; [exact I |].
  destruct rest as [| d rest]; [| exact Hw3].
  cbn. intro.
  destruct a as [| a].
  - destruct Hnib as [_ [Hpos _]]. inversion Hpos; lia.
  - destruct a as [| a].
    + specialize (H3 eq_refl eq_refl). cbn in H3. lia.
    + apply Hw3. lia.
Qed.

Lemma exc_deep : forall n ws cap rs,
  length ws <= n ->
  dmot ws cap rs ->
  match exc ws cap rs with
  | ExC ws' rs' => nib rs' /\ w3 rs' /\ (length rs' = 2 -> 2 <= rhead rs')
  | ExB ws' rs' => nib rs' /\ w3 rs' /\ rhead rs' = S O /\ 3 <= length rs'
  end.
Proof.
  induction n as [| n IH]; introv Hlen HM;
    destruct HM as [Hnib [Hw3 [Hok [Hf Ht]]]].
  - destruct ws; [| cbn in Hlen; lia ].
    cbn [exc]. destruct cap.
    + destruct (Ht eq_refl) as [T2 T3].
      split; [apply nib_push3, Hnib |].
      split; [apply w3_push3_cap; assumption |].
      intro HL. destruct rs as [| a rest]; [cbn in HL; lia |].
      cbn [push3]. cbn. lia.
    + destruct (Hf eq_refl) as [Hhd _].
      auto.
  - destruct ws as [| a ws].
    { cbn [exc]. destruct cap.
      + destruct (Ht eq_refl) as [T2 T3].
        split; [apply nib_push3, Hnib |].
        split; [apply w3_push3_cap; assumption |].
        intro HL. destruct rs as [| x rest]; [cbn in HL; lia |].
        cbn [push3]. cbn. lia.
      + destruct (Hf eq_refl) as [Hhd _]. auto. }
    destruct ws as [| b ws].
    + destruct a.
      * (* 0 :: nil *)
        cbn [exc]. destruct cap.
        -- destruct (Ht eq_refl) as [T2 T3].
           split; [apply nib_push3, Hnib |].
           split; [apply w3_push3_cap; assumption |].
           intro HL. destruct rs as [| x rest]; [cbn in HL; lia |].
           cbn [push3]. cbn. lia.
        -- destruct (Hf eq_refl) as [Hhd _]. auto.
      * (* 1 :: nil *)
        cbn [exc]. destruct cap.
        -- split; [apply nib_cpush, Hnib |].
           split; [apply w3_cons1, Hw3 |].
           split; [reflexivity |].
           destruct Hnib as [HL _]. cbn. lia.
        -- destruct (Hf eq_refl) as [_ [_ Hno]]. contradiction.
    + cbn in Hlen. assert (Hlen' : length ws <= n) by lia.
      destruct a; destruct b; cbn [exc].
      * (* 0,0 *)
        destruct cap.
        -- (* the CS body: recurse uncapped with head >= 4 *)
           destruct (Ht eq_refl) as [T2 T3].
           apply IH; [exact Hlen' |].
           split; [apply nib_push3, Hnib |].
           split; [apply w3_push3_cap; assumption |].
           split; [eapply wallok_tail, wallok_tail, Hok |].
           split.
           ++ intro. split.
              ** destruct rs as [| x rest];
                   [destruct Hnib as [HL _]; cbn in HL; lia |].
                 cbn [push3]. cbn. lia.
              ** apply wallok_zero_guard.
                 eapply wallok_tail, Hok.
           ++ discriminate.
        -- destruct (Hf eq_refl) as [Hhd _].
           split; [exact Hnib |]. split; [exact Hw3 |]. auto.
      * (* 0,1 *)
        destruct cap.
        -- (* degen: the capped word exits as is *)
           destruct (Ht eq_refl) as [T2 T3].
           split; [exact Hnib |]. split; [exact Hw3 |]. exact T2.
        -- destruct (Hf eq_refl) as [Hhd _].
           split; [exact Hnib |]. split; [exact Hw3 |]. auto.
      * (* 1,0 *)
        destruct cap.
        -- split; [apply nib_cpush, Hnib |].
           split; [apply w3_cons1, Hw3 |].
           split; [reflexivity |].
           destruct Hnib as [HL _]. cbn. lia.
        -- destruct (Hf eq_refl) as [_ [Hno _]].
           exfalso. eapply Hno. reflexivity.
      * (* 1,1: the carry *)
        apply IH; [exact Hlen' |].
        split; [apply nib_cpush, Hnib |].
        split.
        { destruct cap.
          - apply w3_cons1, Hw3.
          - destruct (Hf eq_refl) as [Hhd _].
            destruct rs as [| x rest];
              [destruct Hnib as [HL _]; cbn in HL; lia |].
            cbn [cpush].
            eapply w3_head_ge; [exact Hhd | exact Hw3]. }
        split; [eapply wallok_tail, wallok_tail, Hok |].
        split; [discriminate |].
        intro. split.
        -- intro HL. destruct cap.
           ++ cbn [cpush] in HL. cbn in HL.
              destruct Hnib as [HL2 _]. lia.
           ++ destruct (Hf eq_refl) as [Hhd _].
              destruct rs as [| x rest];
                [destruct Hnib as [HL2 _]; cbn in HL2; lia |].
              cbn in Hhd. cbn [cpush]. cbn. lia.
        -- intro HL. destruct cap.
           ++ destruct rs as [| x rest];
                [destruct Hnib as [HL2 _]; cbn in HL2; lia |].
              cbn [cpush] in HL. cbn in HL.
              intro. cbn [cpush second].
              destruct (Ht eq_refl) as [T2 _].
              apply T2. cbn. lia.
           ++ destruct (Hf eq_refl) as [Hhd _].
              destruct rs as [| x rest];
                [destruct Hnib as [HL2 _]; cbn in HL2; lia |].
              cbn in Hhd. cbn [cpush]. cbn [rhead]. intro Hx. lia.
Qed.

(** ** The assembly.

    Everything reduces to closure: if the invariant is preserved by one
    macro step, the machine never halts. The base case is exact: the
    8-step startup lands on the B-entry MB [1] [4], which satisfies the
    invariant on the nose (wall = a single 1; word = the run of four;
    the absorb relaunch shape with a = 4). *)

Lemma inv_wf : forall s, Inv s -> List.Forall (le 1) (mrs s).
Proof.
  introv HI. destruct s as [ws rs | ws rs]; cbn in HI; tauto.
Qed.

Lemma startup_anchor : c0 -->* mconf (MB (cons 1 nil) (cons 4 nil)).
Proof.
  follow startup.
  cbn [mconf runs].
  rewrite zpad.
  finish.
Qed.

Lemma inv_anchor : Inv (MB (cons 1 nil) (cons 4 nil)).
Proof.
  cbn. repeat split; auto.
Qed.

(** Non-halting, given closure. inv_preserve is the one open obligation:
    Inv s -> mstep s = Some s' -> Inv s'. *)
Lemma nonhalt_from_closure :
  (forall s s', Inv s -> mstep s = Some s' -> Inv s') ->
  ~ halts tm c0.
Proof.
  intro Hpres.
  eapply multistep_nonhalt; [apply startup_anchor |].
  apply progress_nonhalt_cond
    with (i0 := MB (cons 1 nil) (cons 4 nil)) (C := mconf) (P := Inv);
    [| exact inv_anchor].
  intros s HI.
  destruct (inv_safe s HI) as [s' Hs'].
  exists s'. split.
  - apply mstep_sim; [apply inv_wf, HI | exact Hs'].
  - eapply Hpres; eauto.
Qed.

(** ** The carry cascade (architecture A groundwork).

    The wall tail below the working gap is a stack of [0;0;1;1] blocks:
    a binary counter. An insulate excursion entering it with the cap set
    increments it: each block costs one cs (head += 3) and one merging
    carry (head += 1), leaving the cap set for the next block. *)

Fixpoint blocks (k : nat) (rest : list Sym) : list Sym :=
  match k with
  | O => rest
  | S k' => cons 0 (cons 0 (cons 1 (cons 1 (blocks k' rest))))
  end.

Fixpoint iter4 (k : nat) (rs : list nat) : list nat :=
  match k with
  | O => rs
  | S k' => iter4 k' (cpush false (push3 rs))
  end.

Lemma iter4_head : forall k h t, iter4 k (cons h t) = cons (4 * k + h) t.
Proof.
  induction k; introv.
  - reflexivity.
  - cbn [iter4 push3 cpush]. rewrite IHk. f_equal. lia.
Qed.

Lemma exc_blocks : forall k rest rs,
  exc (blocks k rest) true rs = exc rest true (iter4 k rs).
Proof.
  induction k; introv.
  - reflexivity.
  - cbn [blocks exc iter4]. apply IHk.
Qed.

(** ** Iterated macro steps and the lap lemmas. *)

Fixpoint mrun (n : nat) (s : mst) : option mst :=
  match n with
  | O => Some s
  | S n' => match mstep s with
            | Some s' => mrun n' s'
            | None => None
            end
  end.

Lemma mrun_app : forall m n s,
  mrun (m + n) s = match mrun m s with
                   | Some s' => mrun n s'
                   | None => None
                   end.
Proof.
  induction m; introv.
  - reflexivity.
  - cbn [mrun Nat.add]. destruct (mstep s); [apply IHm | reflexivity].
Qed.

(** A pump step: the leading 1-run of a multi word erases, growing the
    wall top by two. *)
Lemma mstep_pump : forall ws rs',
  rs' <> nil ->
  mstep (MC ws (cons (S O) rs')) = Some (MC (cons 1 (cons 1 ws)) rs').
Proof.
  introv H. destruct rs' as [| x t]; [contradiction | reflexivity].
Qed.

Fixpoint wpump (j : nat) (ws : list Sym) : list Sym :=
  match j with
  | O => ws
  | S j' => cons 1 (cons 1 (wpump j' ws))
  end.

Lemma wpump_inner : forall j ws,
  wpump j (cons 1 (cons 1 ws)) = cons 1 (cons 1 (wpump j ws)).
Proof.
  induction j; introv; cbn [wpump]; [reflexivity |].
  now rewrite IHj.
Qed.

Lemma prep_ne : forall j r2 rest, prep j (cons r2 rest) <> nil.
Proof. introv. destruct j; discriminate. Qed.

Lemma mrun_pump : forall j ws r2 rest,
  mrun j (MC ws (prep j (cons r2 rest))) =
  Some (MC (wpump j ws) (cons r2 rest)).
Proof.
  induction j; introv.
  - reflexivity.
  - cbn [mrun prep].
    rewrite mstep_pump by apply prep_ne.
    rewrite IHj.
    now rewrite wpump_inner.
Qed.

(** The skim, named. *)
Lemma mstep_skim : forall ws a rest,
  mstep (MB ws (cons a rest)) = Some (MC ([1]^^(S a) ++ ws) rest).
Proof. reflexivity. Qed.

(** An absorb lap's fill: wall top 2j+2 (even), gap at least 1. The
    excursion folds the top run into the word and hands B the rest. *)
Lemma mstep_absorb : forall j wt L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+2) ++ cons 0 wt) (cons L nil)) =
  Some (MB (cons 1 wt) (prep j (cons (S (3 + L)) nil))).
Proof.
  introv HL.
  replace (([1]^^(2*j+2) ++ cons 0 wt)%list)
    with ((cons 1 ([1]^^(2*j+1) ++ cons 0 wt))%list)
    by (replace (2*j+2) with (S (2*j+1)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  now rewrite (exc_absorb j (3 + L) wt).
Qed.

(** An insulate lap's fill, exiting inside the gap: wall top 2j+5 (odd,
    1 mod 4 in the family since j is odd there), gap at least 4. Two
    carries cap the run, the cs eats two zeros, the bitset exit two
    more. *)
Lemma mstep_insulate_exit : forall j g tail L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+5) ++ [0]^^(4+g) ++ tail) (cons L nil)) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ tail)))
           (push3 (prep (S j) (cons (S (3 + L)) nil)))).
Proof.
  introv HL.
  replace (([1]^^(2*j+5) ++ [0]^^(4+g) ++ tail)%list)
    with ((cons 1 ([1]^^(2*j+4) ++ [0]^^(4+g) ++ tail))%list)
    by (replace (2*j+5) with (S (2*j+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_insulate j (3 + L) ([0]^^(4+g) ++ tail)).
  rewrite (exc_run_t j).
  replace (([0]^^(4+g) ++ tail)%list)
    with ((cons 0 (cons 0 (cons 0 (cons 0 ([0]^^g ++ tail)))))%list)
    by (replace (4+g) with (S (S (S (S g)))) by lia; reflexivity).
  cbn [exc of_exit].
  rewrite prep_comm.
  reflexivity.
Qed.

(** An insulate lap's fill that exhausts the gap: the cascade increments
    the block counter all the way to blank and rebuilds the base. The
    exit head is 4*(k+2) + L' arithmetic via iter4/push3. *)
Lemma mstep_insulate_carry : forall j k L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+5) ++ blocks (S k) nil) (cons L nil)) =
  Some (MC (cons 1 (cons 1 nil))
           (push3 (iter4 (S k) (prep (S j) (cons (S (3 + L)) nil))))).
Proof.
  introv HL.
  replace (([1]^^(2*j+5) ++ blocks (S k) nil)%list)
    with ((cons 1 ([1]^^(2*j+4) ++ blocks (S k) nil))%list)
    by (replace (2*j+5) with (S (2*j+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_insulate j (3 + L) (blocks (S k) nil)).
  rewrite (exc_run_t j).
  rewrite prep_comm.
  change (cons (S O) (prep j (cons (S (3 + L)) nil)))
    with (prep (S j) (cons (S (3 + L)) nil)).
  rewrite exc_blocks.
  reflexivity.
Qed.

(** A bury step: a head run b+4 (at least 4) erases into wall zeros,
    resetting the top to two. *)
Lemma mstep_bury : forall ws b r2 rest,
  mstep (MC ws (cons (S (S (S (S b)))) (cons r2 rest))) =
  Some (MC (cons 1 (cons 1 ([0]^^(S (S (S b))) ++ ws))) (cons r2 rest)).
Proof. reflexivity. Qed.

Lemma wpump_lpow : forall n ws, wpump n ws = ([1]^^(2*n) ++ ws)%list.
Proof.
  induction n; introv.
  - reflexivity.
  - cbn [wpump].
    rewrite IHn.
    replace (2 * S n) with (S (S (2*n))) by lia.
    reflexivity.
Qed.

Lemma lpow_app_assoc : forall m k (X : list Sym),
  (([1]^^(m + k) ++ X)%list) = (([1]^^m ++ ([1]^^k ++ X))%list).
Proof.
  introv. now rewrite lpow_add, <- List.app_assoc.
Qed.

(** A full absorb lap from its entry state (wall top 2, prefix S n):
    pump, fill, skim. Ends with wall top 3 and prefix n. *)
Lemma lapA : forall n wt L,
  Nat.even L = true ->
  mrun (S n + 2) (MC (cons 1 (cons 1 (cons 0 wt))) (prep (S n) (cons L nil))) =
  Some (MC (cons 1 (cons 1 (cons 1 wt))) (prep n (cons (S (3 + L)) nil))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite mrun_pump.
  rewrite wpump_lpow.
  cbn [mrun].
  replace (([1]^^(2 * S n) ++ cons 1 (cons 1 (cons 0 wt)))%list)
    with (([1]^^(2 * S n + 2) ++ cons 0 wt)%list)
    by (rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_absorb (S n) wt L HL).
  cbn [prep mrun].
  rewrite mstep_skim.
  reflexivity.
Qed.

(** A full insulate lap exiting in the gap, from its entry state (wall
    top 3, prefix S n, gap at least 4): pump, fill. Ends at wall top 2
    with the merged head 4 ready to bury. *)
Lemma lapI_exit : forall n g tail L,
  Nat.even L = true ->
  mrun (S n + 1)
    (MC (cons 1 (cons 1 (cons 1 ([0]^^(4+g) ++ tail)))) (prep (S n) (cons L nil))) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ tail)))
           (push3 (prep (S n) (cons (S (3 + L)) nil)))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite mrun_pump.
  rewrite wpump_lpow.
  cbn [mrun].
  replace (([1]^^(2 * S n) ++ cons 1 (cons 1 (cons 1 ([0]^^(4+g) ++ tail))))%list)
    with (([1]^^(2 * n + 5) ++ [0]^^(4+g) ++ tail)%list)
    by (replace (2 * n + 5) with (2 * S n + 3) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_insulate_exit n g tail L HL).
  reflexivity.
Qed.

(** The carry variant: same entry, gap exhausted into k+1 counter
    blocks over blank; the cascade rebuilds the base. *)
Lemma lapI_carry : forall n k L,
  Nat.even L = true ->
  mrun (S n + 1)
    (MC (cons 1 (cons 1 (cons 1 (blocks (S k) nil)))) (prep (S n) (cons L nil))) =
  Some (MC (cons 1 (cons 1 nil))
           (push3 (iter4 (S k) (prep (S n) (cons (S (3 + L)) nil))))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite mrun_pump.
  rewrite wpump_lpow.
  cbn [mrun].
  replace (([1]^^(2 * S n) ++ cons 1 (cons 1 (cons 1 (blocks (S k) nil))))%list)
    with (([1]^^(2 * n + 5) ++ blocks (S k) nil)%list)
    by (replace (2 * n + 5) with (2 * S n + 3) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_insulate_carry n k L HL).
  reflexivity.
Qed.
