(** * The cost layer: every sweep, with its exact raw step count.

    The existing chain is stated at [evstep], which erases step counts
    by construction. This file restates the same walk at [multistep],
    carrying the count, so the orbit can be summed into N_halt.

    busycoq has no [multistep] tactics (execute/step/finish all target
    evstep or progress), so they are built here first.

    Every constant below was measured, not assumed: each leaf rule was
    stated with the count as an evar, discharged by stepping, and the
    filled-in value read back out of the proof term. *)

From BusyCoq Require Import Individual62 Odometer OdometerDip.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

(** * Multistep tactics, mirroring Individual.v's evstep ones. *)

Lemma multistep_0' : forall tm c c', c = c' -> c -[ tm ]->> 0 / c'.
Proof. intros. subst c'. apply multistep_0. Qed.

Ltac finish_c := apply multistep_0'; try (reflexivity || lia_refl).
Ltac step_c := eapply multistep_S; [prove_step | simpl_tape].
Ltac execute_c := introv; repeat (try solve [finish_c]; step_c).
Ltac follow_c H := eapply multistep_trans; [apply H |].
(** [cbn] iota-reduces [3 + k] to [S (S (S k))], which leaves
    [multistep_trans]'s [?a + ?b] with nothing to unify against.
    Supplying the first count fixes it. *)
Ltac follow_ck k H := eapply (multistep_trans _ k); [apply H |].

(** * Leaf rules, with counts. *)

Lemma F_e_left1_c : forall l r,
  l <* <[0;1;1;1] <{{F}} r -[ tm ]->> 4 / l <{{F}} [0;1;1;1] *> r.
Proof. execute_c. Qed.

Lemma F_f_left1_c : forall l r,
  l <* <[1;1;1;1] <{{F}} r -[ tm ]->> 4 / l <{{A}} [1;1;1;1] *> r.
Proof. execute_c. Qed.

Lemma F_x0_bounce_c : forall (y : sym) l r,
  l <* <[y;1;0;1] <{{F}} r -[ tm ]->> 3 / l <* <[y;1;1;1] {{E}}> r.
Proof. destruct y; execute_c. Qed.

Lemma A_O_left1_c : forall l r,
  l <* <[0;1;0;1] <{{A}} r -[ tm ]->> 8 / l <{{C}} [1;1;1;1] *> r.
Proof. execute_c. Qed.

Lemma A_f_left1_c : forall l r,
  l <* <[1;1;1;1] <{{A}} r -[ tm ]->> 4 / l <{{C}} [1;1;1;1] *> r.
Proof. execute_c. Qed.

Lemma A_e_reflect_c : forall l r,
  l <* <[0;1;1;1] <{{A}} r -[ tm ]->> 7 / l <* <[1;1;0;1] {{E}}> r.
Proof. execute_c. Qed.

Lemma A_a_reflect_c : forall l r,
  l <* <[1;1;0;1] <{{A}} r -[ tm ]->> 11 / l <* <[1;1;0;1] {{E}}> r.
Proof. execute_c. Qed.

Lemma sep_bounce_c : forall l r,
  l <* <[0;1;0;1] <{{C}} r -[ tm ]->> 7 / l <* <[1;1;1;1] {{E}}> r.
Proof. execute_c. Qed.

Lemma C_e_probe_c : forall l r,
  l <* <[0;1;1;1] <{{C}} r -[ tm ]->> 4 / l <{{D}} [1;1;1;1] *> r.
Proof. execute_c. Qed.

Lemma C_a_left1_c : forall l r,
  l <* <[1;1;0;1] <{{C}} r -[ tm ]->> 4 / l <{{C}} [1;1;0;1] *> r.
Proof. execute_c. Qed.

Lemma C_f_left1_c : forall l r,
  l <* <[1;1;1;1] <{{C}} r -[ tm ]->> 4 / l <{{F}} [1;1;1;1] *> r.
Proof. execute_c. Qed.

Lemma D_O_reflect_c : forall l r,
  l <* <[0;1;0;1] <{{D}} r -[ tm ]->> 3 / l <* <[0;1;1;1] {{C}}> r.
Proof. execute_c. Qed.

Lemma D_e_reflect_c : forall l r,
  l <* <[0;1;1;1] <{{D}} r -[ tm ]->> 3 / l <* <[0;1;0;1] {{C}}> r.
Proof. execute_c. Qed.

Lemma D_a_reflect_c : forall l r,
  l <* <[1;1;0;1] <{{D}} r -[ tm ]->> 3 / l <* <[1;1;1;1] {{C}}> r.
Proof. execute_c. Qed.

Lemma C_f_redip_c : forall l r,
  l {{C}}> [1;1;1;1] *> r -[ tm ]->> 1 / l <{{F}} [1;1;1;1] *> r.
Proof. execute_c. Qed.

Lemma virgin_reflect0_c : forall l,
  l {{E}}> 1 >> const 0 -[ tm ]->> 9 / l <{{C}} 1 >> 1 >> 1 >> 0 >> const 0.
Proof. execute_c. Qed.

Lemma virgin_finish_c : forall l r,
  l {{E}}> 1 >> 1 >> 1 >> 0 >> r -[ tm ]->> 4 / l <* <[0;1;0;1] {{C}}> r.
Proof. execute_c. Qed.

Lemma edge_start_c : forall l,
  l <* <[0;1;0;1] {{C}}> const 0 -[ tm ]->> 4 / l <* <[0;1;1;1] {{C}}> 1 >> const 0.
Proof. execute_c. Qed.

(** The E-pass over one glyph: 4 for every glyph, which is what makes
    the outward pass exactly 4 per crossed cell. *)
Lemma E_toggle_c : forall g l r,
  l {{E}}> graw g *> r -[ tm ]->> 4 / l <* grev (toggle g) {{E}}> r.
Proof. destruct g; execute_c. Qed.

(** * The four tail passes: 4 steps per block, linear in n. *)

Lemma F_es_left_c : forall n l r,
  l <* <[0;1;1;1]^^n <{{F}} r -[ tm ]->> (4 * n) / l <{{F}} [0;1;1;1]^^n *> r.
Proof.
  induction n; introv.
  - cbn. finish_c.
  - replace (4 * S n) with (S (S (S (S (4 * n))))) by lia.
    step_c. step_c. step_c. step_c.
    change (0 >> 1 >> 1 >> 1 >> ([0;1;1;1]^^n *> r))
      with ([0;1;1;1] *> [0;1;1;1]^^n *> r).
    rewrite <- lpow_shift'.
    apply IHn.
Qed.

Lemma E_es_right_c : forall n l r,
  l {{E}}> [0;1;1;1]^^n *> r -[ tm ]->> (4 * n) / l <* <[1;1;0;1]^^n {{E}}> r.
Proof.
  induction n; introv.
  - cbn. finish_c.
  - replace (4 * S n) with (S (S (S (S (4 * n))))) by lia.
    step_c. step_c. step_c. step_c.
    change (1 >> 0 >> 1 >> 1 >> ([1;0;1;1]^^n *> l))
      with ([1;0;1;1] *> [1;0;1;1]^^n *> l).
    rewrite <- lpow_shift'.
    apply IHn.
Qed.

Lemma C_as_left_c : forall n l r,
  l <* <[1;1;0;1]^^n <{{C}} r -[ tm ]->> (4 * n) / l <{{C}} [1;1;0;1]^^n *> r.
Proof.
  induction n; introv.
  - cbn. finish_c.
  - replace (4 * S n) with (S (S (S (S (4 * n))))) by lia.
    step_c. step_c. step_c. step_c.
    change (1 >> 1 >> 0 >> 1 >> ([1;1;0;1]^^n *> r))
      with ([1;1;0;1] *> [1;1;0;1]^^n *> r).
    rewrite <- lpow_shift'.
    apply IHn.
Qed.

Lemma E_as_right_c : forall n l r,
  l {{E}}> [1;1;0;1]^^n *> r -[ tm ]->> (4 * n) / l <* <[0;1;1;1]^^n {{E}}> r.
Proof.
  induction n; introv.
  - cbn. finish_c.
  - replace (4 * S n) with (S (S (S (S (4 * n))))) by lia.
    step_c. step_c. step_c. step_c.
    change (1 >> 1 >> 1 >> 0 >> ([1;1;1;0]^^n *> l))
      with ([1;1;1;0] *> [1;1;1;0]^^n *> l).
    rewrite <- lpow_shift'.
    apply IHn.
Qed.

(** * The cost of one inward transition, indexed exactly as [instep]. *)

Definition icost (s : wstate) (g : glyph) : nat :=
  match s, g with
  | wF, gO => 3 | wF, ge => 4  | wF, ga => 3  | wF, gf => 4
  | wA, gO => 8 | wA, ge => 7  | wA, ga => 11 | wA, gf => 4
  | wC, gO => 7 | wC, ge => 4  | wC, ga => 4  | wC, gf => 4
  | wD, gO => 3 | wD, ge => 3  | wD, ga => 3
  | _, _ => 0
  end.

(** The cost walk: same recursion as [dip_go], accumulating steps.
    In [wE] the outward pass pays 4 per crossed cell. *)
Fixpoint dip_go_cost (fuel : nat) (s : wstate) (deep shallow : list glyph)
    : option nat :=
  match fuel with
  | O => None
  | S fuel =>
    match s with
    | wE => Some (4 * length shallow)
    | wCr =>
      match shallow with
      | gf :: _ =>
        match dip_go_cost fuel wF deep shallow with
        | Some k => Some (1 + k)
        | None => None
        end
      | _ => None
      end
    | _ =>
      match deep with
      | [] => None
      | g :: deep' =>
        match instep s g with
        | Some (g', s') =>
          match (if is_inward s'
                 then dip_go_cost fuel s' deep' (g' :: shallow)
                 else dip_go_cost fuel s' (g' :: deep') shallow) with
          | Some k => Some (icost s g + k)
          | None => None
          end
        | None => None
        end
      end
    end
  end.

Definition dip_cost (W : list glyph) : option nat :=
  dip_go_cost (12 * length W + 60) wF W [].

(** * Soundness, with the count. *)

Lemma unwind_sound_c : forall (shallow deep : list glyph) bl r,
  gside bl deep {{E}}> gright shallow r
  -[ tm ]->> (4 * length shallow) / gside bl (unwind shallow deep) {{E}}> r.
Proof.
  induction shallow as [| a shallow IH]; introv.
  - cbn. finish_c.
  - cbn [length unwind gright].
    replace (4 * S (length shallow)) with (4 + 4 * length shallow) by lia.
    follow_c E_toggle_c.
    change (grev (toggle a) *> gside bl deep)
      with (gside bl (toggle a :: deep)).
    apply IH.
Qed.

Lemma dip_go_sound_c : forall fuel s deep shallow W' k bl r,
  dip_go fuel s deep shallow = Some W' ->
  dip_go_cost fuel s deep shallow = Some k ->
  wcfg s bl deep shallow r -[ tm ]->> k / gside bl W' {{E}}> r.
Proof.
  induction fuel; introv H Hk. { discriminate. }
  destruct s; cbn in H; cbn [dip_go_cost instep is_inward icost] in Hk.
  - (* wF *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn [dip_go_cost instep is_inward icost] in Hk; cbn.
    + destruct (dip_go_cost fuel wE (ge :: deep') shallow) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 3 (F_x0_bounce_c 0).
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wF deep' (ge :: shallow)) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 4 F_e_left1_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wE (gf :: deep') shallow) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 3 (F_x0_bounce_c 1).
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wA deep' (gf :: shallow)) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 4 F_f_left1_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
  - (* wA *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn [dip_go_cost instep is_inward icost] in Hk; cbn.
    + destruct (dip_go_cost fuel wC deep' (gf :: shallow)) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 8 A_O_left1_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wE (ga :: deep') shallow) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 7 A_e_reflect_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wE (ga :: deep') shallow) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 11 A_a_reflect_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wC deep' (gf :: shallow)) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 4 A_f_left1_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
  - (* wC *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn [dip_go_cost instep is_inward icost] in Hk; cbn.
    + destruct (dip_go_cost fuel wE (gf :: deep') shallow) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 7 sep_bounce_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wD deep' (gf :: shallow)) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 4 C_e_probe_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wC deep' (ga :: shallow)) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 4 C_a_left1_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wF deep' (gf :: shallow)) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 4 C_f_left1_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
  - (* wD *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn [dip_go_cost instep is_inward icost] in Hk; cbn.
    + destruct (dip_go_cost fuel wCr (ge :: deep') shallow) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 3 D_O_reflect_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wCr (gO :: deep') shallow) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 3 D_e_reflect_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + destruct (dip_go_cost fuel wCr (gf :: deep') shallow) eqn:E1;
        [| discriminate].
      injection Hk as <-. follow_ck 3 D_a_reflect_c.
      apply (IHfuel _ _ _ _ _ _ _ H E1).
    + discriminate.
  - (* wCr *)
    destruct shallow as [| g sh]; [discriminate |].
    destruct g; try discriminate.
    cbn.
    destruct (dip_go_cost fuel wF deep (gf :: sh)) eqn:E1; [| discriminate].
    injection Hk as <-. follow_ck (1%nat) C_f_redip_c.
    apply (IHfuel _ _ _ _ _ _ _ H E1).
  - (* wE *)
    injection H as <-. injection Hk as <-. apply unwind_sound_c.
Qed.

Corollary dip_sound_c : forall W W' k bl,
  dip W = Some W' ->
  dip_cost W = Some k ->
  forall r, gside bl W <{{F}} r -[ tm ]->> k / gside bl W' {{E}}> r.
Proof.
  introv H Hk. intros r. unfold dip in H. unfold dip_cost in Hk.
  pose proof (dip_go_sound_c _ _ _ _ _ _ bl r H Hk) as X.
  cbn [wcfg gright] in X. exact X.
Qed.

(** * THE COUNTED SWEEP.

    One sweep costs 16 steps per tail block (four passes of four), 25
    fixed for the two edge turnarounds, and the dip's own cost. *)
Theorem sweep_theorem_c : forall Z Z' n k,
  dip (gf :: Z) = Some (gO :: Z') ->
  dip_cost (gf :: Z) = Some k ->
  anchor (gf :: Z) n -[ tm ]->> (16 * S n + 25 + k) / anchor (gf :: Z') (S n).
Proof.
  introv H Hk.
  unfold anchor.
  (* [step_c] runs simpl_tape, whose [simpl] would expand the whole
     count; keep the tail opaque across that one step. *)
  remember (4 * S n + (k + (4 * S n + (9 + (4 * S n +
            (7 + (4 * S n + 4))))))) as REST eqn:HR.
  replace (16 * S n + 25 + k) with (4 + (1 + REST)) by lia.
  follow_c edge_start_c.
  step_c.
  rewrite HR.
  follow_c (F_es_left_c (S n)).
  follow_c (dip_sound_c _ _ _ (const 0) H Hk).
  follow_c (E_es_right_c (S n)).
  follow_c virgin_reflect0_c.
  follow_c (C_as_left_c (S n)).
  follow_c sep_bounce_c.
  follow_c (E_as_right_c (S n)).
  follow_ck 4 virgin_finish_c.
  finish_c.
Qed.
