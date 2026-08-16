(** * The span cost: what a whole counting era costs.

    [OdometerCost] gives one sweep its exact step count, as a function
    of the glyph string. This file turns that into arithmetic: the cost
    of a dip on [spellW G v T] depends only on the digits of v, and the
    cost of a whole span of sweeps is then a closed recursion on G.

    Measured model (OdometerSpanProbe.v, confirmed at depths 1, 2, 3):

      dip_cost (spellW G v T) = 20 + 24 * c(v) + fbyte (term v)

    where c(v) counts trailing 15-digits and term(v) is the first
    non-15 digit. The 20 is entering (12 inward over the separator and
    head cell, 8 unwinding them); each crossed full group costs 24
    (12 inward as C->F->A->C over fff, 12 unwinding its three cells);
    fbyte is the terminating group's own inward cost plus 4 per cell
    it crossed.

    Note this is NOT tools/nhalt.mjs's closed form S(X, G), which counts
    values with exactly j trailing 15s using floor division. Recursing
    on the digits instead keeps everything structural and lets
    vm_compute do the work in at most G steps. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerOrbit
                            OdometerCost.
From Coq Require Import Lia NArith.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope N_scope.

(** The terminating group's cost. Measured, one entry per byte. *)
Definition fbyte (b : N) : nat :=
  match b with
  | 0 => 7  | 1 => 11 | 2 => 7  | 3 => 19
  | 4 => 7  | 5 => 11 | 6 => 7  | 7 => 23
  | 8 => 7  | 9 => 11 | 10 => 7 | 11 => 19
  | 12 => 7 | 13 => 11 | _ => 7
  end.

(** The cost of the group walk, entered in wC, excluding the [4 * |sh|]
    owed for cells already crossed before the groups. *)
Fixpoint zwcost (G : nat) (v : N) : nat :=
  match G with
  | O => 0%nat
  | S G' =>
    if (v mod 16 =? 15)%N
    then (24 + zwcost G' (v / 16))%nat
    else fbyte (v mod 16)
  end.

(** * Fuel monotonicity for the cost walk. *)

Lemma dip_go_cost_mono : forall fuel fuel' s deep shallow k,
  dip_go_cost fuel s deep shallow = Some k ->
  (fuel <= fuel')%nat ->
  dip_go_cost fuel' s deep shallow = Some k.
Proof.
  induction fuel; introv H Hle. { discriminate. }
  destruct fuel' as [| fuel']; [lia |].
  cbn in H; cbn.
  destruct s.
  1-4: (destruct deep as [| g deep']; [discriminate |];
        destruct (instep _ g) as [[g' s'] |]; [| discriminate];
        destruct (is_inward s');
        [ destruct (dip_go_cost fuel s' deep' (g' :: shallow)) eqn:E;
            [| discriminate];
          rewrite (IHfuel fuel' _ _ _ _ E ltac:(lia)); exact H
        | destruct (dip_go_cost fuel s' (g' :: deep') shallow) eqn:E;
            [| discriminate];
          rewrite (IHfuel fuel' _ _ _ _ E ltac:(lia)); exact H ]).
  - destruct shallow as [| g sh]; [discriminate |].
    destruct g; try discriminate.
    destruct (dip_go_cost fuel wF deep (gf :: sh)) eqn:E; [| discriminate].
    rewrite (IHfuel fuel' _ _ _ _ E ltac:(lia)). exact H.
  - exact H.
Qed.

(** * Crossing a full group costs 24: 12 inward, 12 on the way out. *)

Lemma zwcost_cross15 : forall fuel rest sh k,
  dip_go_cost fuel wC rest (gf :: gf :: gf :: sh) = Some k ->
  dip_go_cost (S (S (S fuel))) wC (gcells 15 ++ rest) sh = Some (12 + k)%nat.
Proof.
  intros fuel rest sh k H.
  cbn [gcells app dip_go_cost instep is_inward icost].
  rewrite H. reflexivity.
Qed.

(** * The fifteen terminating bytes. Each exits inside its own group. *)

(** [cbn] cannot unfold the fuel fixpoint under a delta whitelist, and
    full reduction leaves the two sides equal but not syntactically so
    (4 * S n vs 4 + 4 * n), hence the [lia]. *)
(** Minimal fuel: a terminating byte crosses at most three cells and
    then stops in wE, so four levels always suffice. Stating it with
    symbolic [fuel] instead of [60 + ...] keeps [cbn] from expanding
    sixty successors fifteen times over, which timed out at 900s. *)
Ltac zbyte :=
  intros fuel G' v T sh Hb; cbn [zgroups zwcost]; rewrite Hb;
  cbn; f_equal; lia.

Lemma zwc_0 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 0 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_1 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 1 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_2 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 2 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_3 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 3 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_4 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 4 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_5 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 5 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_6 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 6 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_7 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 7 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_8 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 8 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_9 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 9 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_10 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 10 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_11 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 11 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_12 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 12 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_13 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 13 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

Lemma zwc_14 : forall fuel (G' : nat) (v : N) T sh, v mod 16 = 14 ->
  dip_go_cost (S (S (S (S fuel)))) wC (zgroups (S G') v ++ T) sh
  = Some (zwcost (S G') v + 4 * length sh)%nat.
Proof. zbyte. Qed.

(** * The walk cost, for any v whose carry stays inside the groups. *)

Lemma zwalk_cost : forall G v T sh,
  v mod 16 ^ N.of_nat G <> 16 ^ N.of_nat G - 1 ->
  dip_go_cost (60 + (12 * G + length sh))%nat wC (zgroups G v ++ T) sh
  = Some (zwcost G v + 4 * length sh)%nat.
Proof.
  induction G as [| G' IHG']; intros v T sh Hne.
  { exfalso. apply Hne. cbn. rewrite N.mod_1_r. reflexivity. }
  assert (Hc : v mod 16 = 0 \/ v mod 16 = 1 \/ v mod 16 = 2 \/
               v mod 16 = 3 \/ v mod 16 = 4 \/ v mod 16 = 5 \/
               v mod 16 = 6 \/ v mod 16 = 7 \/ v mod 16 = 8 \/
               v mod 16 = 9 \/ v mod 16 = 10 \/ v mod 16 = 11 \/
               v mod 16 = 12 \/ v mod 16 = 13 \/ v mod 16 = 14 \/
               v mod 16 = 15)
    by (pose proof (byte_lt v); lia).
  destruct Hc as
    [Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|[Hb|Hb]]]]]]]]]]]]]]].
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_0 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_1 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_2 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_3 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_4 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_5 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_6 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_7 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_8 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_9 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_10 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_11 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_12 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_13 _ G' v T sh Hb).
  - replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (S (56 + (12 * S G' + length sh))))))%nat by lia.
    exact (zwc_14 _ G' v T sh Hb).
  - (* the carry: byte 15, cross in three steps, recurse on v/16.
       Fuel slack 69 (not 60) so the three crossed cells are paid for,
       exactly as zwalk does; dip_go_cost_mono absorbs the difference. *)
    cbn [zwcost zgroups]. rewrite Hb. cbn [N.eqb Pos.eqb].
    replace (60 + (12 * S G' + length sh))%nat
      with (S (S (S (69 + (12 * G' + length sh)))))%nat by lia.
    replace (24 + zwcost G' (v / 16) + 4 * length sh)%nat
      with (12 + (zwcost G' (v / 16)
                  + 4 * length (gf :: gf :: gf :: sh)))%nat
      by (cbn [length]; lia).
    rewrite <- app_assoc.
    apply zwcost_cross15.
    eapply dip_go_cost_mono.
    + apply (IHG' (v / 16) T (gf :: gf :: gf :: sh)
               (carry_desc v G' Hne Hb)).
    + cbn [length]. lia.
Qed.

(** * The dip cost of a spelled counter, as pure digit arithmetic. *)

Definition zcost (G : nat) (v : N) : nat := (20 + zwcost G v)%nat.

(** Entering the zone: F over the separator (4), A over the head cell (8).
    Stated with SYMBOLIC fuel so cbn unfolds exactly two levels. Writing
    this inline instead cost 45 minutes of divergence: [dip_cost]'s fuel
    is [12 * length W + 60], and cbn expands the 60 into successors and
    then grinds the fixpoint through all of them. *)
Lemma dip_enter_cost : forall fuel rest k,
  dip_go_cost fuel wC rest [gf; gf] = Some k ->
  dip_go_cost (S (S fuel)) wF (gf :: gO :: rest) [] = Some (12 + k)%nat.
Proof.
  intros fuel rest k H.
  cbn [dip_go_cost instep is_inward icost]. rewrite H. reflexivity.
Qed.

Lemma dip_cost_spell : forall G v T,
  v mod 16 ^ N.of_nat G <> 16 ^ N.of_nat G - 1 ->
  dip_cost (spellW G v T) = Some (zcost G v).
Proof.
  intros G v T Hne. unfold zcost.
  replace (20 + zwcost G v)%nat
    with (12 + (zwcost G v + 4 * length [gf; gf]))%nat
    by (cbn [length]; lia).
  unfold dip_cost, spellW.
  eapply dip_go_cost_mono.
  - apply dip_enter_cost. apply (zwalk_cost G v T [gf; gf] Hne).
  - cbn [length]. rewrite app_length, zgroups_len. lia.
Qed.
