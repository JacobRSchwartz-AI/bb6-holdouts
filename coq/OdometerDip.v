(** * The dip: the Odometer's one move, as an abstract machine.

    Validated against the raw machine 5999/5999 (tools/dipwalk.mjs,
    P-2026-08-14-o): every sweep's inward walk is a six-state machine
    over 4-cell glyphs. Raw spellings (left-to-right, value bits
    reversed): O=0101 e=0111 a=1101 f=1111. *)

From BusyCoq Require Import Individual62 Odometer.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".

(** * The missing single-block rules (census rows not yet in Odometer.v). *)

(** F walks left over one e, byte-preserved. *)
Lemma F_e_left1 : forall l r,
  l <* <[0;1;1;1] <{{F}} r -->* l <{{F}} [0;1;1;1] *> r.
Proof. execute. Qed.

(** A walks left over one f, byte-preserved, exits C. *)
Lemma A_f_left1 : forall l r,
  l <* <[1;1;1;1] <{{A}} r -->* l <{{C}} [1;1;1;1] *> r.
Proof. execute. Qed.

(** A meets e: reflect, carry lands (e -> a). *)
Lemma A_e_reflect : forall l r,
  l <* <[0;1;1;1] <{{A}} r -->* l <* <[1;1;0;1] {{E}}> r.
Proof. execute. Qed.

(** A meets a: reflect, a preserved — THE MELT / collapse primitive. *)
Lemma A_a_reflect : forall l r,
  l <* <[1;1;0;1] <{{A}} r -->* l <* <[1;1;0;1] {{E}}> r.
Proof. execute. Qed.

(** C walks left over one a, byte-preserved. *)
Lemma C_a_left1 : forall l r,
  l <* <[1;1;0;1] <{{C}} r -->* l <{{C}} [1;1;0;1] *> r.
Proof. execute. Qed.

(** C meets e: converts it to f and probes deeper as D. *)
Lemma C_e_probe : forall l r,
  l <* <[0;1;1;1] <{{C}} r -->* l <{{D}} [1;1;1;1] *> r.
Proof. execute. Qed.

(** D probes O: carry lands two deep (O -> e), reflect as C. *)
Lemma D_O_reflect : forall l r,
  l <* <[0;1;0;1] <{{D}} r -->* l <* <[0;1;1;1] {{C}}> r.
Proof. execute. Qed.

(** D probes a: a -> f, reflect as C. *)
Lemma D_a_reflect : forall l r,
  l <* <[1;1;0;1] <{{D}} r -->* l <* <[1;1;1;1] {{C}}> r.
Proof. execute. Qed.

(** D probes e: e -> O, reflect as C. *)
Lemma D_e_reflect : forall l r,
  l <* <[0;1;1;1] <{{D}} r -->* l <* <[0;1;0;1] {{C}}> r.
Proof. execute. Qed.

(** The returning C meets the f it made and turns back inward as F. *)
Lemma C_f_redip : forall l r,
  l {{C}}> [1;1;1;1] *> r -->* l <{{F}} [1;1;1;1] *> r.
Proof. execute. Qed.

(** * Glyphs and the abstract dip machine. *)

Inductive glyph := gO | ge | ga | gf.

(** Raw spelling, left-to-right. *)
Definition graw (g : glyph) : list sym :=
  match g with
  | gO => [0;1;0;1] | ge => [0;1;1;1] | ga => [1;1;0;1] | gf => [1;1;1;1]
  end.

(** Reversed spelling, for pushing onto a left stream. *)
Definition grev (g : glyph) : list sym := rev (graw g).

(** A glyph string in walk order (separator first = rightmost on tape),
    interpreted as a left stream on top of a base [bl]. *)
Fixpoint gside (bl : side) (W : list glyph) : side :=
  match W with
  | [] => bl
  | g :: W' => gside bl W' <* grev g
  end.

(** The same cells as a right-side prefix (walk order = nearest first). *)
Fixpoint gright (W : list glyph) (r : side) : side :=
  match W with
  | [] => r
  | g :: W' => graw g *> gright W' r
  end.

(** The E-crossing toggle (value XOR 5). *)
Definition toggle (g : glyph) : glyph :=
  match g with gO => gf | gf => gO | ge => ga | ga => ge end.

Inductive wstate := wF | wA | wC | wD | wCr | wE.

Definition is_inward (s : wstate) : bool :=
  match s with wF | wA | wC | wD => true | _ => false end.

(** The inward rule table (the census, sealed over 100M steps). *)
Definition instep (s : wstate) (g : glyph) : option (glyph * wstate) :=
  match s, g with
  | wF, ge => Some (ge, wF) | wF, gf => Some (gf, wA)
  | wF, gO => Some (ge, wE) | wF, ga => Some (gf, wE)
  | wA, gO => Some (gf, wC) | wA, gf => Some (gf, wC)
  | wA, ge => Some (ga, wE) | wA, ga => Some (ga, wE)
  | wC, ga => Some (ga, wC) | wC, gf => Some (gf, wF)
  | wC, gO => Some (gf, wE) | wC, ge => Some (gf, wD)
  | wD, gO => Some (ge, wCr) | wD, ga => Some (gf, wCr) | wD, ge => Some (gO, wCr)
  | _, _ => None
  end.

(** The walk, as a zipper: [deep] = the current cell and everything
    deeper (head = current); [shallow] = crossed cells (head = nearest).
    In [wE] mode, [deep] doubles as the accumulating result. *)
Fixpoint dip_go (fuel : nat) (s : wstate) (deep shallow : list glyph)
    : option (list glyph) :=
  match fuel with
  | O => None
  | S fuel =>
    match s with
    | wE =>
      match shallow with
      | [] => Some deep
      | g :: sh => dip_go fuel wE (toggle g :: deep) sh
      end
    | wCr =>
      match shallow with
      | gf :: _ => dip_go fuel wF deep shallow
      | _ => None
      end
    | _ =>
      match deep with
      | [] => None
      | g :: deep' =>
        match instep s g with
        | Some (g', s') =>
          if is_inward s'
          then dip_go fuel s' deep' (g' :: shallow)
          else dip_go fuel s' (g' :: deep') shallow
        | None => None
        end
      end
    end
  end.

(** The dip: enter at the right end of W in state F. *)
Definition dip (W : list glyph) : option (list glyph) :=
  dip_go (12 * length W + 60) wF W [].

(** * Soundness: the abstract walk is the machine. *)

(** E walks right over any glyph, toggling it (one bridge lemma over
    the four cases). *)
Lemma E_toggle : forall g l r,
  l {{E}}> graw g *> r -->* l <* grev (toggle g) {{E}}> r.
Proof. destruct g; execute. Qed.

(** The tape configuration of a walk state. *)
Definition wcfg (s : wstate) (bl : side) (deep shallow : list glyph)
    (r : side) : Q * tape :=
  match s with
  | wF => gside bl deep <{{F}} gright shallow r
  | wA => gside bl deep <{{A}} gright shallow r
  | wC => gside bl deep <{{C}} gright shallow r
  | wD => gside bl deep <{{D}} gright shallow r
  | wCr => gside bl deep {{C}}> gright shallow r
  | wE => gside bl deep {{E}}> gright shallow r
  end.

Lemma dip_go_sound : forall fuel s deep shallow W' bl r,
  dip_go fuel s deep shallow = Some W' ->
  wcfg s bl deep shallow r -->* gside bl W' {{E}}> r.
Proof.
  induction fuel; introv H. { discriminate. }
  destruct s; cbn in H.
  - (* wF *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn.
    + follow (F_x0_bounce 0). apply (IHfuel _ _ _ _ _ _ H).
    + follow F_e_left1. apply (IHfuel _ _ _ _ _ _ H).
    + follow (F_x0_bounce 1). apply (IHfuel _ _ _ _ _ _ H).
    + follow F_f_left1. apply (IHfuel _ _ _ _ _ _ H).
  - (* wA *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn.
    + follow A_O_left1. apply (IHfuel _ _ _ _ _ _ H).
    + follow A_e_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + follow A_a_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + follow A_f_left1. apply (IHfuel _ _ _ _ _ _ H).
  - (* wC *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn.
    + follow sep_bounce. apply (IHfuel _ _ _ _ _ _ H).
    + follow C_e_probe. apply (IHfuel _ _ _ _ _ _ H).
    + follow C_a_left1. apply (IHfuel _ _ _ _ _ _ H).
    + follow C_f_left1. apply (IHfuel _ _ _ _ _ _ H).
  - (* wD *)
    destruct deep as [| g deep']; [discriminate |].
    destruct g; cbn in H; cbn.
    + follow D_O_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + follow D_e_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + follow D_a_reflect. apply (IHfuel _ _ _ _ _ _ H).
    + discriminate.
  - (* wCr *)
    destruct shallow as [| g sh]; [discriminate |].
    destruct g; try discriminate.
    cbn.
    follow C_f_redip. apply (IHfuel _ _ _ _ _ _ H).
  - (* wE *)
    destruct shallow as [| g sh].
    + injection H as <-. cbn. finish.
    + cbn.
      follow E_toggle. apply (IHfuel _ _ _ _ _ _ H).
Qed.

(** The dip, from the anchor side: entering the string in state F. *)
Corollary dip_sound : forall W W' bl,
  dip W = Some W' ->
  forall r, gside bl W <{{F}} r -->* gside bl W' {{E}}> r.
Proof.
  introv H. intros r. unfold dip in H.
  apply (dip_go_sound _ _ _ _ _ bl r) in H.
  cbn in H. exact H.
Qed.

(** * The universal sweep theorem. *)

(** An anchor: glyph string (separator-first), tail of n e's, edge O,
    head facing the blank half in state C. *)
Definition anchor (W : list glyph) (n : nat) : Q * tape :=
  gside (const 0) W <* <[0;1;1;1]^^n <* <[0;1;0;1] {{C}}> const 0.

Lemma edge_start_plus : forall l,
  l <* <[0;1;0;1] {{C}}> const 0 -->+ l <* <[0;1;1;1] {{C}}> 1 >> const 0.
Proof. introv. start_progress. Qed.

(** One sweep: if the dip succeeds on the string, the anchor steps to
    the next anchor — tail one longer, separator restored, zone as the
    dip left it. This is the ONLY tape-level theorem the proof needs;
    everything else is arithmetic about [dip]. *)
Theorem sweep_theorem : forall Z Z' n,
  dip (gf :: Z) = Some (gO :: Z') ->
  anchor (gf :: Z) n -->+ anchor (gf :: Z') (S n).
Proof.
  introv H.
  unfold anchor.
  eapply progress_evstep_trans.
  { apply edge_start_plus. }
  step.
  follow (F_es_left (S n)).
  follow (dip_sound _ _ (const 0) H).
  follow (E_es_right (S n)).
  follow virgin_reflect0.
  follow (C_as_left (S n)).
  follow sep_bounce.
  follow (E_as_right (S n)).
  follow virgin_finish.
  finish.
Qed.

(** * The invariant, and non-halt from it. *)

(** A glyph string is safe if its dips succeed forever. *)
CoInductive safe : list glyph -> Prop :=
| safe_step : forall Z Z',
    dip (gf :: Z) = Some (gO :: Z') ->
    safe (gf :: Z') ->
    safe (gf :: Z).

Theorem nonhalt_of_safe : forall Z n,
  safe (gf :: Z) -> ~ halts tm (anchor (gf :: Z) n).
Proof.
  introv HS.
  apply progress_nonhalt_cond with
    (A := (list glyph * nat)%type)
    (C := fun '(Z0, n0) => anchor (gf :: Z0) n0)
    (P := fun '(Z0, n0) => safe (gf :: Z0))
    (i0 := (Z, n)).
  - intros [Z0 n0] HP.
    inversion HP as [? Z' Hdip HS']; subst.
    exists (Z', S n0). split.
    + apply sweep_theorem. exact Hdip.
    + exact HS'.
  - exact HS.
Qed.
