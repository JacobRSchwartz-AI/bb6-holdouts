(** * The fatal sweep, with its exact step count.

    The dying walk is a DIFFERENT function from the ordinary dip:
    [dip_go_dies] detects the walk running off the left end of the
    written tape in state C, which is the halt. So it needs its own
    cost mirror; [dip_go_cost] does not cover it.

    One extra step is charged where the walk falls off: C over blank
    goes to D over blank, and D/0 is the halt transition. *)

(* nat only: no NArith, or its notations capture every + and literal *)
From BusyCoq Require Import Individual62 Odometer OdometerDip OdometerCost.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

(** Prefixing a counted run onto a counted halt. *)
Lemma halts_in_multistep : forall c c' j k,
  c -[ tm ]->> j / c' ->
  halts_in tm c' k ->
  halts_in tm c (j + k).
Proof.
  intros c c' j k H1 [ch [H2 H3]].
  exists ch. split; [| exact H3].
  eapply multistep_trans; eassumption.
Qed.

(** Falling off the written tape in state C: one step to the halt. *)
Lemma death_blank_c : forall (r : side),
  halts_in tm (const 0 <{{C}} r) 1%nat.
Proof.
  intro r. unfold halts_in. eexists. split.
  - step_c. finish_c.
  - reflexivity.
Qed.

(** The cost mirror of [dip_go_dies], same recursion exactly. *)
Fixpoint dip_go_dies_cost (fuel : nat) (s : wstate) (deep shallow : list glyph)
    : option nat :=
  match fuel with
  | O => None
  | S fuel =>
    match s with
    | wE => None
    | wCr =>
      match shallow with
      | gf :: _ =>
        match dip_go_dies_cost fuel wF deep shallow with
        | Some k => Some (1 + k)
        | None => None
        end
      | _ => None
      end
    | _ =>
      match deep with
      | [] => match s with wC => Some 1%nat | _ => None end
      | g :: deep' =>
        match instep s g with
        | Some (_, wE) => None
        | Some (g', wCr) =>
          match dip_go_dies_cost fuel wCr (g' :: deep') shallow with
          | Some k => Some (icost s g + k)
          | None => None
          end
        | Some (g', s') =>
          match dip_go_dies_cost fuel s' deep' (g' :: shallow) with
          | Some k => Some (icost s g + k)
          | None => None
          end
        | None => None
        end
      end
    end
  end.

Definition dies_cost (W : list glyph) : option nat :=
  dip_go_dies_cost (12 * length W + 60) wF W [].

Ltac dcase L c :=
  eapply (halts_in_multistep _ _ c);
  [ cbn [wcfg gside gright graw grev toggle]; follow_ck c L; finish_c
  | eassumption ].

Lemma dip_go_dies_cost_sound : forall fuel s deep shallow r k,
  dip_go_dies_cost fuel s deep shallow = Some k ->
  halts_in tm (wcfg s (const 0) deep shallow r) k.
Proof.
  induction fuel; introv Hk. { discriminate. }
  destruct s; cbn [dip_go_dies_cost] in Hk.
  - (* wF *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn [instep] in Hk; try discriminate.
    + destruct (dip_go_dies_cost fuel wF deep' (ge :: shallow)) eqn:E;
        [| discriminate].
      injection Hk as <-. cbn [icost].
      eapply (halts_in_multistep _ _ 4).
      * cbn. follow_ck 4 F_e_left1_c. finish_c.
      * apply (IHfuel _ _ _ _ _ E).
    + destruct (dip_go_dies_cost fuel wA deep' (gf :: shallow)) eqn:E;
        [| discriminate].
      injection Hk as <-. cbn [icost].
      eapply (halts_in_multistep _ _ 4).
      * cbn. follow_ck 4 F_f_left1_c. finish_c.
      * apply (IHfuel _ _ _ _ _ E).
  - (* wA *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn [instep] in Hk; try discriminate.
    + destruct (dip_go_dies_cost fuel wC deep' (gf :: shallow)) eqn:E;
        [| discriminate].
      injection Hk as <-. cbn [icost].
      eapply (halts_in_multistep _ _ 8).
      * cbn. follow_ck 8 A_O_left1_c. finish_c.
      * apply (IHfuel _ _ _ _ _ E).
    + destruct (dip_go_dies_cost fuel wC deep' (gf :: shallow)) eqn:E;
        [| discriminate].
      injection Hk as <-. cbn [icost].
      eapply (halts_in_multistep _ _ 4).
      * cbn. follow_ck 4 A_f_left1_c. finish_c.
      * apply (IHfuel _ _ _ _ _ E).
  - (* wC: the fall-off lives here *)
    destruct deep as [| g deep'].
    + injection Hk as <-. cbn. apply death_blank_c.
    + destruct g; cbn [instep] in Hk; try discriminate.
      * destruct (dip_go_dies_cost fuel wD deep' (gf :: shallow)) eqn:E;
          [| discriminate].
        injection Hk as <-. cbn [icost].
        eapply (halts_in_multistep _ _ 4).
        { cbn. follow_ck 4 C_e_probe_c. finish_c. }
        { apply (IHfuel _ _ _ _ _ E). }
      * destruct (dip_go_dies_cost fuel wC deep' (ga :: shallow)) eqn:E;
          [| discriminate].
        injection Hk as <-. cbn [icost].
        eapply (halts_in_multistep _ _ 4).
        { cbn. follow_ck 4 C_a_left1_c. finish_c. }
        { apply (IHfuel _ _ _ _ _ E). }
      * destruct (dip_go_dies_cost fuel wF deep' (gf :: shallow)) eqn:E;
          [| discriminate].
        injection Hk as <-. cbn [icost].
        eapply (halts_in_multistep _ _ 4).
        { cbn. follow_ck 4 C_f_left1_c. finish_c. }
        { apply (IHfuel _ _ _ _ _ E). }
  - (* wD *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn [instep] in Hk; try discriminate.
    + destruct (dip_go_dies_cost fuel wCr (ge :: deep') shallow) eqn:E;
        [| discriminate].
      injection Hk as <-. cbn [icost].
      eapply (halts_in_multistep _ _ 3).
      * cbn. follow_ck 3 D_O_reflect_c. finish_c.
      * apply (IHfuel _ _ _ _ _ E).
    + destruct (dip_go_dies_cost fuel wCr (gO :: deep') shallow) eqn:E;
        [| discriminate].
      injection Hk as <-. cbn [icost].
      eapply (halts_in_multistep _ _ 3).
      * cbn. follow_ck 3 D_e_reflect_c. finish_c.
      * apply (IHfuel _ _ _ _ _ E).
    + destruct (dip_go_dies_cost fuel wCr (gf :: deep') shallow) eqn:E;
        [| discriminate].
      injection Hk as <-. cbn [icost].
      eapply (halts_in_multistep _ _ 3).
      * cbn. follow_ck 3 D_a_reflect_c. finish_c.
      * apply (IHfuel _ _ _ _ _ E).
  - (* wCr *)
    destruct shallow as [| g sh]; [discriminate |].
    destruct g; try discriminate.
    destruct (dip_go_dies_cost fuel wF deep (gf :: sh)) eqn:E; [| discriminate].
    injection Hk as <-.
    eapply (halts_in_multistep _ _ 1).
    + cbn. follow_ck (1%nat) C_f_redip_c. finish_c.
    + apply (IHfuel _ _ _ _ _ E).
  - (* wE *) discriminate.
Qed.

(** The fatal sweep out of an anchor: edge turnaround (4), one step,
    the four-per-block walk down the tail, then the dying walk. *)
Theorem death_sweep_c : forall Z n k,
  dies_cost (gf :: Z) = Some k ->
  halts_in tm (anchor (gf :: Z) n) (4 + (1 + (4 * S n + k))).
Proof.
  introv Hk. unfold anchor.
  eapply (halts_in_multistep _ _ 4). { apply edge_start_c. }
  eapply (halts_in_multistep _ _ 1). { step_c. finish_c. }
  eapply (halts_in_multistep _ _ (4 * S n)).
  { apply (F_es_left_c (S n) (gside (const 0) (gf :: Z)) (1 >> const 0)). }
  unfold dies_cost in Hk.
  apply (dip_go_dies_cost_sound _ _ _ _ ([0;1;1;1]^^(S n) *> 1 >> const 0) _ Hk).
Qed.
