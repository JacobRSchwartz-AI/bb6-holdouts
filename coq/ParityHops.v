From BusyCoq Require Import Individual62.
From BusyCoq Require Import Parity.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
Set Default Goal Selector "!".

(** mstep-level equations closing the gaps named in notes/parity.md's
    finish sequence (V6: digit-bury variants, absorb_nil, insulate_degen,
    top-4 pump re-entries). Every shape below was checked against exc's
    Fixpoint and against concrete orbit instances (tools/parity-close.mjs)
    before being encoded here. *)

(** The absorb lap when the wall below the even 1-run is EMPTY: exc's
    blank branch (exc_absorb_nil) rather than exc_absorb's `cons 0 wt`.
    Orbit instance: j=18, L=16 (MC [1]^38 [16] -> MB [1] [1^18,20]). *)
Lemma mstep_absorb_nil : forall j L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+2)) (cons L nil)) =
  Some (MB (cons 1 nil) (prep j (cons (S (3 + L)) nil))).
Proof.
  introv HL.
  replace ([1]^^(2*j+2))
    with (cons 1 ([1]^^(2*j+1)))
    by (replace (2*j+2) with (S (2*j+1)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  now rewrite (exc_absorb_nil j (3 + L)).
Qed.

(** The insulate lap whose 0-gap below the odd 1-run has length 1: exc's
    (0,1) branch fires with cap still set, so the exit carries THREE
    explicit ones (not exc_insulate_exit's two) which merge with
    whatever 1-run follows. No push3: the gap is spent before any
    (0,0) pair is ever seen. Orbit instance: j=16, L=4 (top 37, gap 1,
    the following run happens to be a single 1 -- the top-4 birth). *)
Lemma mstep_insulate_degen : forall j rest L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+5) ++ cons 0 (cons 1 rest)) (cons L nil)) =
  Some (MC (cons 1 (cons 1 (cons 1 rest)))
           (prep (S j) (cons (S (3 + L)) nil))).
Proof.
  introv HL.
  replace (([1]^^(2*j+5) ++ cons 0 (cons 1 rest))%list)
    with ((cons 1 ([1]^^(2*j+4) ++ cons 0 (cons 1 rest)))%list)
    by (replace (2*j+5) with (S (2*j+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_insulate j (3 + L) (cons 0 (cons 1 rest))).
  rewrite (exc_run_t j).
  cbn [exc of_exit].
  rewrite prep_comm.
  reflexivity.
Qed.

(** The insulate lap whose gap is exactly 3: one (0,0) pair is consumed
    (push3, cap flips to false) before the (0,1) branch fires, so the
    exit carries only TWO explicit ones -- same rs-transformation as
    mstep_insulate_exit's, one level short of its second (0,0) pair.
    Orbit instance: j=202, L=20 (top 409, gap 3). *)
Lemma mstep_insulate_gap3 : forall j rest2 L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+5) ++ [0;0;0] ++ cons 1 rest2) (cons L nil)) =
  Some (MC (cons 1 (cons 1 rest2))
           (push3 (prep (S j) (cons (S (3 + L)) nil)))).
Proof.
  introv HL.
  replace (([1]^^(2*j+5) ++ [0;0;0] ++ cons 1 rest2)%list)
    with ((cons 1 ([1]^^(2*j+4) ++ [0;0;0] ++ cons 1 rest2))%list)
    by (replace (2*j+5) with (S (2*j+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_insulate j (3 + L) ([0;0;0] ++ cons 1 rest2)%list).
  rewrite (exc_run_t j).
  cbn [exc of_exit].
  rewrite prep_comm.
  reflexivity.
Qed.

(** The insulate lap whose odd run IS the entire wall: exc's nil branch,
    cap still set, mirroring mstep_absorb_nil the way mstep_insulate_exit
    mirrors mstep_absorb -- found by the coverage scan (--family showed no
    dispatch class this shape could explain), not in the original target
    list. Orbit instances: j=0,L=4; j=4,L=12; j=16,L=20 (all three
    consecutive occurrences before ev150). *)
Lemma mstep_insulate_nil : forall j L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*j+5)) (cons L nil)) =
  Some (MC (cons 1 (cons 1 nil))
           (push3 (prep (S j) (cons (S (3 + L)) nil)))).
Proof.
  introv HL.
  replace ([1]^^(2*j+5))
    with ((cons 1 ([1]^^(2*j+4) ++ nil))%list)
    by (rewrite List.app_nil_r;
        replace (2*j+5) with (S (2*j+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_insulate j (3 + L) nil).
  rewrite (exc_run_t j).
  cbn [exc of_exit].
  rewrite prep_comm.
  reflexivity.
Qed.

Print Assumptions mstep_absorb_nil.
Print Assumptions mstep_insulate_degen.
Print Assumptions mstep_insulate_gap3.
Print Assumptions mstep_insulate_nil.

(** ** rs=nil coverage: the mstep Fixpoint's `MC ws nil` arm.

    A DIFFERENT match arm from `cons L nil`: no `rest`, no separator, ws
    dispatches straight against a fresh accumulator `cons 3 nil`. No
    `Nat.even` guard -- there is no L to test -- and the arm is
    definitionally the c=0 instance of the singleton arm (`3 + 0` reduces
    to `3`, `Nat.even 0` to `true`), which is why the statement below is a
    clean L=0 mirror of mstep_absorb even though it unfolds a distinct
    Fixpoint clause. Both wt sub-shapes occur on the concrete orbit: of the
    10 rs=nil dispatches in the first 1.9M events, 9 are wt<>nil, the 10th
    (ev=1, off the startup anchor) is wt=nil. No insulate (odd-top)
    instance occurs -- see exc_insulate_rs_ge2 below for why. *)

(** Orbit instance: ev=8, j=6, wt = [0;1;1]
    (MC [1]^14 [0;1;1] [] -> MB [1;0;1;1] [1^6,4]). *)
Lemma mstep_absorb_rs0 : forall j wt,
  mstep (MC ([1]^^(2*j+2) ++ cons 0 wt) nil) =
  Some (MB (cons 1 wt) (prep j (cons 4 nil))).
Proof.
  introv.
  replace (([1]^^(2*j+2) ++ cons 0 wt)%list)
    with ((cons 1 ([1]^^(2*j+1) ++ cons 0 wt))%list)
    by (replace (2*j+2) with (S (2*j+1)) by lia; reflexivity).
  cbn [mstep].
  now rewrite (exc_absorb j 3 wt).
Qed.

(** Orbit instance: ev=1, j=2, off the startup anchor itself
    (MC [1]^6 [] -> MB [1] [1;1;4]). *)
Lemma mstep_absorb_nil_rs0 : forall j,
  mstep (MC ([1]^^(2*j+2)) nil) =
  Some (MB (cons 1 nil) (prep j (cons 4 nil))).
Proof.
  introv.
  replace ([1]^^(2*j+2))
    with (cons 1 ([1]^^(2*j+1)))
    by (replace (2*j+2) with (S (2*j+1)) by lia; reflexivity).
  cbn [mstep].
  now rewrite (exc_absorb_nil j 3).
Qed.

(** ** The insulate-family rs=nil mirror does not exist: an impossibility
    result, not a gap. cpush/push3 never shrink their list argument --
    they bump the head in place, or (only starting from nil) grow it from
    0 to 1 -- so exc's threaded rs component is never shorter coming out
    than it went in. *)
Lemma prep_len : forall j rs, length rs <= length (prep j rs).
Proof.
  induction j; introv; cbn [prep].
  - lia.
  - specialize (IHj rs). cbn [length]. lia.
Qed.

Lemma cpush_len : forall cap rs, length rs <= length (cpush cap rs).
Proof.
  introv. destruct cap; cbn [cpush].
  - cbn [length]. lia.
  - destruct rs; cbn [length]; lia.
Qed.

Lemma push3_len : forall rs, length rs <= length (push3 rs).
Proof. introv. destruct rs; cbn [push3 length]; lia. Qed.

(** The general fact behind the impossibility argument: exc's rs component
    is length-monotone under any wall, any cap, any rs -- mirrors exc_pos's
    induction exactly, tracking length instead of positivity. *)
Lemma exc_len_mono : forall n ws cap rs,
  length ws <= n ->
  length rs <= length (xrs (exc ws cap rs)).
Proof.
  induction n; introv Hlen.
  - destruct ws; [| cbn in Hlen; lia].
    cbn [exc]. destruct cap; cbn [xrs]; [apply push3_len | lia].
  - destruct ws as [| a ws'].
    + cbn [exc]. destruct cap; cbn [xrs]; [apply push3_len | lia].
    + destruct a.
      * destruct ws' as [| b ws''].
        { cbn [exc]. destruct cap; cbn [xrs]; [apply push3_len | lia]. }
        destruct b.
        { cbn [exc]. destruct cap.
          - transitivity (length (push3 rs));
              [apply push3_len | apply IHn; cbn in Hlen |- *; lia].
          - cbn [xrs]. lia. }
        { cbn [exc]. destruct cap; cbn [xrs]; lia. }
      * destruct ws' as [| b ws''].
        { cbn [exc xrs]. apply cpush_len. }
        destruct b.
        { cbn [exc xrs]. apply cpush_len. }
        { cbn [exc].
          transitivity (length (cpush cap rs));
            [apply cpush_len | apply IHn; cbn in Hlen |- *; lia]. }
Qed.

(** THE IMPOSSIBILITY. exc_insulate already lands rs at length exactly 2
    (`cons 1 (cons (S x) nil)`) before a single cell of wt is examined;
    exc_len_mono shows that floor can only rise from there, whatever wt is.
    Since mstep_skim is the only route to an rs=nil MC state, and it needs
    its MB's rs to already be a singleton, no insulate-shaped dispatch --
    any of the six named wt shapes above, or any other -- can ever be the
    immediate predecessor of an mstep (MC ws nil) call. The odd-top mirror
    of mstep_absorb_rs0 isn't merely unobserved in the 5M-event scan: it's
    unreachable by construction. No orbit instance -- this is the
    non-existence half of the coverage gap. *)
Lemma exc_insulate_rs_ge2 : forall j x wt,
  2 <= length (xrs (exc ([1]^^(2*j+4) ++ wt) false (cons x nil))).
Proof.
  introv.
  rewrite (exc_insulate j x wt).
  rewrite (exc_run_t j).
  assert (Hb : length wt <= length wt) by lia.
  pose proof (exc_len_mono (length wt) wt true
    (prep j (cons (S O) (cons (S x) nil))) Hb) as H.
  pose proof (prep_len j (cons (S O) (cons (S x) nil))) as Hp.
  cbn [length] in Hp.
  lia.
Qed.

Print Assumptions mstep_absorb_rs0.
Print Assumptions mstep_absorb_nil_rs0.
Print Assumptions prep_len.
Print Assumptions cpush_len.
Print Assumptions push3_len.
Print Assumptions exc_len_mono.
Print Assumptions exc_insulate_rs_ge2.
