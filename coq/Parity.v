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

(** ** Startup: c0 to the first structured configuration. *)

Lemma startup : c0 -->* const 0 <* <[1] {{B}}> [1; 1; 1; 1] *> const 0.
Proof. execute. Qed.
