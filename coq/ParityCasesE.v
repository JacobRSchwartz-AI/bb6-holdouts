From BusyCoq Require Import Individual62.
From BusyCoq Require Import Parity.
From BusyCoq Require Import ParityHops.
From BusyCoq Require Import ParityHops2.
From BusyCoq Require Import ParityCasesA.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
Set Default Goal Selector "!".

Lemma even_double : forall m, Nat.even (2 * m) = true.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    cbn [Nat.even]. exact IH.
Qed.

(** A targeted 1-step unfold: cbn[mrun] on a goal that still has an
    S-headed multi-step remainder sitting in a sibling match branch (e.g.
    right after splitting `1 + S n` via mrun_app) eagerly peels into that
    sibling too, destroying the exact `mrun (S n) _` shape a later
    mrun_pump/mb_pump_skim rewrite needs. Rewriting by this lemma instead
    touches only the literal `mrun 1 s` occurrence. *)
Lemma mrun1 : forall s, mrun 1 s = mstep s.
Proof. introv. cbn [mrun]. destruct (mstep s); reflexivity. Qed.

Lemma epoch_p0_open : forall (SW : list Sym) (m : nat),
  mrun (4 + (S (S m) + (1 + S m)))
    (MC (cons 1 (cons 1 SW)) (cons 4 (cons (2 * m) nil))) =
  Some (MC ([1]^^(6 + 2 * m) ++ SW) (cons 8 nil)).
Proof.
  introv.
  assert (HL : Nat.even (2 * m) = true) by apply even_double.
  rewrite mrun_app.
  cbn [mrun prep].
  change 4 with (S (S (S (S 0)))) at 1.
  rewrite mstep_bury by discriminate.
  cbv iota.
  replace ((cons 1 (cons 1 (([0]^^(S (S (S 0))) ++ cons 1 (cons 1 SW))%list))))
    with (([1]^^(2 * 0 + 2) ++ cons 0 (cons 0 (cons 0 (cons 1 (cons 1 SW)))))%list)
    by reflexivity.
  cbn [mrun prep].
  rewrite (mstep_absorb 0 (cons 0 (cons 0 (cons 1 (cons 1 SW)))) (2 * m) HL).
  cbv iota.
  cbn [mrun prep].
  rewrite mstep_skim.
  cbv iota.
  cbn [mrun prep].
  replace (([1]^^(S (S (3 + 2 * m))) ++ cons 1 (cons 0 (cons 0 (cons 1 (cons 1 SW)))))%list)
    with (([1]^^(2 * S (S m) + 2) ++ cons 0 (cons 0 (cons 1 (cons 1 SW))))%list)
    by (replace (2 * S (S m) + 2) with ((S (S (3 + 2 * m))) + 1) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_absorb_rs0 (S (S m)) (cons 0 (cons 1 (cons 1 SW)))).
  cbv iota.
  rewrite mrun_app.
  rewrite (mb_pump_skim (S m) (cons 1 (cons 0 (cons 1 (cons 1 SW)))) 4 nil).
  cbv iota.
  rewrite wpump_lpow.
  replace (([1]^^(2 * S (S m)) ++ cons 1 (cons 0 (cons 1 (cons 1 SW))))%list)
    with (([1]^^(2 * m + 5) ++ cons 0 (cons 1 (cons 1 SW)))%list)
    by (replace (2 * m + 5) with (2 * S (S m) + 1) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite mrun_app.
  rewrite (mrun1 (MC ([1]^^(2 * m + 5) ++ cons 0 (cons 1 (cons 1 SW))) (cons 4 nil))).
  rewrite (mstep_insulate_degen m (cons 1 SW) 4) by reflexivity.
  cbv iota.
  rewrite (mrun_pump (S m) (cons 1 (cons 1 (cons 1 (cons 1 SW)))) (S (3 + 4)) nil).
  rewrite wpump_lpow.
  replace (([1]^^(2 * S m) ++ cons 1 (cons 1 (cons 1 (cons 1 SW))))%list)
    with (([1]^^(6 + 2 * m) ++ SW)%list)
    by (replace (6 + 2 * m) with (2 * S m + 4) by lia;
        rewrite lpow_app_assoc; reflexivity).
  reflexivity.
Qed.

Print Assumptions even_double.
Print Assumptions epoch_p0_open.

(** ** epoch:p0-blank -- the ANCHOR case: F.p = 0, F.stack = [].
    Orbit instance ev5: {top:2,stack:[],H:4,W:[],p:0,L:8} ->
    {top:2,stack:[],H:4,W:[],p:4,L:16}, n=24 -- this IS the real hop out of
    the anchor's first boundary (replayed and matched exactly, see task
    report). General form derived (not guessed) by replaying L in
    {0,2,8,16,24,40}: p'=L/2, L'=16 (a FIXED constant, not "2L"), n=3*(L/2)+12
    in every instance. Proof: epoch_p0_open (SW=nil) lands
    [1]^^(6+2m) [8], a blank-tailed state; mstep_absorb_nil then
    mb_pump_skim then mstep_insulate_nil close it out exactly as the
    startup-shaped chunkBig/chunkCascade family closes chunkTerm, but from
    a p=0 (no leading prep) entry instead of p>=2. *)
Lemma epoch_p0_blank : forall m,
  mrun ((4 + (S (S m) + (1 + S m))) + (1 + (S (S m) + 1)))
    (MC (cons 1 (cons 1 nil)) (cons 4 (cons (2 * m) nil))) =
  Some (MC (cons 1 (cons 1 nil)) (cons 4 (prep m (cons 16 nil)))).
Proof.
  introv.
  rewrite (mrun_app (4 + (S (S m) + (1 + S m))) (1 + (S (S m) + 1))
             (MC (cons 1 (cons 1 nil)) (cons 4 (cons (2 * m) nil)))).
  assert (Hopen : mrun (4 + (S (S m) + (1 + S m)))
                    (MC (cons 1 (cons 1 nil)) (cons 4 (cons (2 * m) nil))) =
                  Some (MC ([1]^^(6 + 2 * m) ++ nil) (cons 8 nil)))
    by apply (epoch_p0_open nil m).
  rewrite Hopen.
  cbv iota.
  rewrite List.app_nil_r.
  rewrite mrun_app.
  rewrite (mrun1 (MC ([1]^^(6 + 2 * m)) (cons 8 nil))).
  replace ([1]^^(6 + 2 * m)) with ([1]^^(2 * S (S m) + 2)) by (f_equal; lia).
  rewrite (mstep_absorb_nil (S (S m)) 8) by reflexivity.
  cbv iota.
  rewrite mrun_app.
  rewrite (mb_pump_skim (S m) (cons 1 nil) (S (3 + 8)) nil).
  cbv iota.
  rewrite wpump_lpow.
  replace (([1]^^(2 * S (S m)) ++ cons 1 nil)%list)
    with (([1]^^(2 * m + 5) ++ nil)%list)
    by (replace (2 * m + 5) with (2 * S (S m) + 1) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite List.app_nil_r.
  rewrite (mrun1 (MC ([1]^^(2 * m + 5)) (cons (S (3 + 8)) nil))).
  rewrite (mstep_insulate_nil m (S (3 + 8))) by reflexivity.
  cbv iota.
  reflexivity.
Qed.

Print Assumptions epoch_p0_blank.

(** ** epoch:p0-big -- F.p = 0, F.stack[0] = (gap >= 5, run = 2), the
    single-entry case with no absorbed chain (the H4 counterpart to
    p0-big being the "chain length 0" instance of p0-deepChain's family;
    proven directly here since digitBirth is not involved).
    Orbit instance: {top:2,stack:[[10,2]],H:4,W:[],p:0,L:88} ->
    {top:2,stack:[[5,2]],H:4,W:[],p:44,L:16}, n=144 (replayed exactly,
    plus a synthetic L=8/gap=10 instance at n=24, both matching this
    lemma's closed form with m=L/2, g=gap-5). Same p'=L/2, L'=16 as
    p0-blank; the gap shift -5 comes from mstep_insulate_exit's own -4
    (its own `g` slot) composed with the one 0 mstep_absorb's `cons 0 wt`
    always spends immediately after H's own bury, matching the JSON's
    "gap shifts -5" language for a gap>=6 chain terminator. `deeper` is
    carried through untouched and fully generic (never inspected), so
    this covers any stack depth below the single gap>=5 entry, not just
    the JSON's own depth-1 example. *)
Lemma epoch_p0_big : forall (deeper : list Sym) (g m : nat),
  mrun ((4 + (S (S m) + (1 + S m))) + (1 + (S (S m) + 1)))
    (MC (cons 1 (cons 1 ([0]^^(g + 5) ++ cons 1 (cons 1 deeper))))
        (cons 4 (cons (2 * m) nil))) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ cons 1 (cons 1 deeper))))
           (cons 4 (prep m (cons 16 nil)))).
Proof.
  introv.
  rewrite (mrun_app (4 + (S (S m) + (1 + S m))) (1 + (S (S m) + 1))
             (MC (cons 1 (cons 1 ([0]^^(g + 5) ++ cons 1 (cons 1 deeper))))
                 (cons 4 (cons (2 * m) nil)))).
  assert (Hopen : mrun (4 + (S (S m) + (1 + S m)))
                    (MC (cons 1 (cons 1 ([0]^^(g + 5) ++ cons 1 (cons 1 deeper))))
                        (cons 4 (cons (2 * m) nil))) =
                  Some (MC ([1]^^(6 + 2 * m) ++
                              ([0]^^(g + 5) ++ cons 1 (cons 1 deeper))) (cons 8 nil)))
    by apply (epoch_p0_open ([0]^^(g + 5) ++ cons 1 (cons 1 deeper)) m).
  rewrite Hopen.
  cbv iota.
  rewrite mrun_app.
  rewrite (mrun1 (MC ([1]^^(6 + 2 * m) ++
                        ([0]^^(g + 5) ++ cons 1 (cons 1 deeper))) (cons 8 nil))).
  replace (([1]^^(6 + 2 * m) ++ ([0]^^(g + 5) ++ cons 1 (cons 1 deeper)))%list)
    with (([1]^^(2 * S (S m) + 2) ++
             cons 0 ([0]^^(g + 4) ++ cons 1 (cons 1 deeper)))%list)
    by (replace (2 * S (S m) + 2) with (6 + 2 * m) by lia;
        replace (g + 5) with (S (g + 4)) by lia;
        reflexivity).
  rewrite (mstep_absorb (S (S m)) ([0]^^(g + 4) ++ cons 1 (cons 1 deeper)) 8)
    by reflexivity.
  cbv iota.
  rewrite mrun_app.
  rewrite (mb_pump_skim (S m) (cons 1 ([0]^^(g + 4) ++ cons 1 (cons 1 deeper)))
             (S (3 + 8)) nil).
  cbv iota.
  rewrite wpump_lpow.
  replace (([1]^^(2 * S (S m)) ++
              cons 1 ([0]^^(g + 4) ++ cons 1 (cons 1 deeper)))%list)
    with (([1]^^(2 * m + 5) ++ ([0]^^(4 + g) ++ cons 1 (cons 1 deeper)))%list)
    by (replace (2 * m + 5) with (2 * S (S m) + 1) by lia;
        replace (g + 4) with (4 + g) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mrun1 (MC ([1]^^(2 * m + 5) ++ ([0]^^(4 + g) ++ cons 1 (cons 1 deeper)))
                    (cons (S (3 + 8)) nil))).
  rewrite (mstep_insulate_exit m g (cons 1 (cons 1 deeper)) (S (3 + 8)))
    by reflexivity.
  cbv iota.
  reflexivity.
Qed.

Print Assumptions epoch_p0_big.

(** ** epoch:p0-chain -- F.p = 0, F.stack = [(gap=2, run=2)], nothing
    deeper: the one absorbed-(2,2)-entry case. Orbit instance:
    {top:2,stack:[[2,2]],H:4,W:[],p:0,L:32} ->
    {top:2,stack:[],H:4,W:[],p:16,L:24}, n=97 (replayed exactly, plus a
    synthetic L=8 instance at n=37, both matching m=L/2, n=5m+17). Proof:
    epoch_p0_open lands on a wall with the (2,2) entry's own encoding as
    tail; mstep_absorb + mb_pump_skim + mstep_insulate_degen (a SECOND
    application of the same three-lemma shape epoch_p0_open's own middle
    used, this time exactly at gap=2 so the wall reduces to blank rather
    than exiting) plus mrun_pump re-close the (2,2) into a fresh blank
    top-4 state carrying L=16; from there the closing three lemmas are
    LITERALLY p0-blank's own closing round (mstep_absorb_nil,
    mb_pump_skim, mstep_insulate_nil) replayed at L=16 instead of L=8,
    landing L'=16+8=24. Scoped to the JSON's own depth: a nonempty deeper
    stack under the (2,2) would recurse through this same dispatch again
    (blank vs gap=2 vs gap>=5) and is not proven here. *)
Lemma epoch_p0_chain : forall m : nat,
  mrun ((4 + (S (S m) + (1 + S m))) +
        (1 + (S (S m) + (1 + (S m + (1 + (S (S m) + 1)))))))
    (MC (cons 1 (cons 1 (cons 0 (cons 0 (cons 1 (cons 1 nil))))))
        (cons 4 (cons (2 * m) nil))) =
  Some (MC (cons 1 (cons 1 nil)) (cons 4 (prep m (cons 24 nil)))).
Proof.
  introv.
  rewrite (mrun_app (4 + (S (S m) + (1 + S m)))
             (1 + (S (S m) + (1 + (S m + (1 + (S (S m) + 1))))))
             (MC (cons 1 (cons 1 (cons 0 (cons 0 (cons 1 (cons 1 nil))))))
                 (cons 4 (cons (2 * m) nil)))).
  assert (Hopen : mrun (4 + (S (S m) + (1 + S m)))
                    (MC (cons 1 (cons 1 (cons 0 (cons 0 (cons 1 (cons 1 nil))))))
                        (cons 4 (cons (2 * m) nil))) =
                  Some (MC ([1]^^(6 + 2 * m) ++
                              cons 0 (cons 0 (cons 1 (cons 1 nil)))) (cons 8 nil)))
    by apply (epoch_p0_open (cons 0 (cons 0 (cons 1 (cons 1 nil)))) m).
  rewrite Hopen.
  cbv iota.
  rewrite mrun_app.
  rewrite (mrun1 (MC ([1]^^(6 + 2 * m) ++
                        cons 0 (cons 0 (cons 1 (cons 1 nil)))) (cons 8 nil))).
  replace (([1]^^(6 + 2 * m) ++ cons 0 (cons 0 (cons 1 (cons 1 nil))))%list)
    with (([1]^^(2 * S (S m) + 2) ++ cons 0 (cons 0 (cons 1 (cons 1 nil))))%list)
    by (do 2 f_equal; lia).
  rewrite (mstep_absorb (S (S m)) (cons 0 (cons 1 (cons 1 nil))) 8) by reflexivity.
  cbv iota.
  rewrite mrun_app.
  rewrite (mb_pump_skim (S m) (cons 1 (cons 0 (cons 1 (cons 1 nil)))) (S (3 + 8)) nil).
  cbv iota.
  rewrite wpump_lpow.
  replace (([1]^^(2 * S (S m)) ++ cons 1 (cons 0 (cons 1 (cons 1 nil))))%list)
    with (([1]^^(2 * m + 5) ++ cons 0 (cons 1 (cons 1 nil)))%list)
    by (replace (2 * m + 5) with (2 * S (S m) + 1) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite mrun_app.
  rewrite (mrun1 (MC ([1]^^(2 * m + 5) ++ cons 0 (cons 1 (cons 1 nil)))
                    (cons (S (3 + 8)) nil))).
  rewrite (mstep_insulate_degen m (cons 1 nil) (S (3 + 8))) by reflexivity.
  cbv iota.
  rewrite mrun_app.
  rewrite (mrun_pump (S m) (cons 1 (cons 1 (cons 1 (cons 1 nil))))
             (S (3 + S (3 + 8))) nil).
  rewrite wpump_lpow.
  replace (([1]^^(2 * S m) ++ cons 1 (cons 1 (cons 1 (cons 1 nil))))%list)
    with (([1]^^(6 + 2 * m) ++ nil)%list)
    by (replace (6 + 2 * m) with (2 * S m + 4) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite List.app_nil_r.
  rewrite mrun_app.
  rewrite (mrun1 (MC ([1]^^(6 + 2 * m)) (cons (S (3 + S (3 + 8))) nil))).
  replace ([1]^^(6 + 2 * m)) with ([1]^^(2 * S (S m) + 2)) by (f_equal; lia).
  rewrite (mstep_absorb_nil (S (S m)) (S (3 + S (3 + 8)))) by reflexivity.
  cbv iota.
  rewrite mrun_app.
  rewrite (mb_pump_skim (S m) (cons 1 nil) (S (3 + S (3 + S (3 + 8)))) nil).
  cbv iota.
  rewrite wpump_lpow.
  replace (([1]^^(2 * S (S m)) ++ cons 1 nil)%list)
    with (([1]^^(2 * m + 5) ++ nil)%list)
    by (replace (2 * m + 5) with (2 * S (S m) + 1) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite List.app_nil_r.
  rewrite (mrun1 (MC ([1]^^(2 * m + 5)) (cons (S (3 + S (3 + S (3 + 8)))) nil))).
  rewrite (mstep_insulate_nil m (S (3 + S (3 + S (3 + 8))))) by reflexivity.
  cbv iota.
  reflexivity.
Qed.

Print Assumptions epoch_p0_chain.
