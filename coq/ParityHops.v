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
