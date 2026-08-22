From BusyCoq Require Import Individual62.
From BusyCoq Require Import Parity.
From BusyCoq Require Import ParityHops.
From BusyCoq Require Import ParityHops2.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
Set Default Goal Selector "!".

(** Composed hop lemmas for the "phase 1" boundary shapes of
    tools/chunkstep-cases.json (keys phase1:closed=1, phase1:closed=2).
    Every mstep firing here is the rest<>nil general branch of `mstep`,
    which (per notes/parity.md's chunkstep successor map) is uniform for
    ANY popped rs value v: pushing 0^(v+1) onto the wall always makes the
    excursion's first two cells 0,0 with cap=false, an immediate exit --
    v=1 merges into the current top run (mstep_pump); v=4+b buries it under
    a fresh top-2 with gap 3+b below (mstep_bury). No excursion looping
    (exc_run_t/carries) is involved anywhere in this file: every named
    lemma below composes ONLY mstep_bury and mrun_pump, both already
    proved in coq/Parity.v. Validated against a literal replay of mstep
    (tools/parity-close.mjs's mstepL, snapshotted) for every JSON example
    below before encoding; n matches exactly in each case. *)

(** One boundary-to-boundary hop where exactly one rs symbol (the head, H)
    closes: H's own bury plants a fresh (gap 3+b, run top) stack entry,
    then j >= 0 further "1" pops grow the new top by 2 each, and the walk
    lands the moment it meets the next symbol without consuming it (r2,
    the new H). p and L never move: rest is untouched.
    Orbit instances (chunkstep-cases.json phase1:closed=1, all replayed):
      j=1: {top:2,stack:[],H:4,W:[1,9],p:22,L:104}
        -> {top:4,stack:[[3,2]],H:9,W:[],p:22,L:104}, n=2
      j=1: {top:2,stack:[],H:8,W:[1,9],p:6,L:168}
        -> {top:4,stack:[[7,2]],H:9,W:[],p:6,L:168}, n=2
      j=0: {top:2,stack:[],H:4,W:[9],p:84,L:76}
        -> {top:2,stack:[[3,2]],H:9,W:[],p:84,L:76}, n=1 *)
Lemma phase1_closed1 : forall top wt b j r2 rest,
  mrun (S j) (MC ([1]^^top ++ wt) (cons (S (S (S (S b)))) (prep j (cons r2 rest)))) =
  Some (MC ([1]^^(2 * j + 2) ++ [0]^^(S (S (S b))) ++ [1]^^top ++ wt) (cons r2 rest)).
Proof.
  introv.
  cbn [mrun].
  rewrite (mstep_bury ([1]^^top ++ wt) b (prep j (cons r2 rest))) by apply prep_ne.
  cbv iota.
  rewrite (mrun_pump j (cons 1 (cons 1 ([0]^^(S (S (S b))) ++ [1]^^top ++ wt))) r2 rest).
  rewrite wpump_lpow.
  replace (([1]^^(2 * j) ++ cons 1 (cons 1 ([0]^^(S (S (S b))) ++ [1]^^top ++ wt)))%list)
    with (([1]^^(2 * j + 2) ++ [0]^^(S (S (S b))) ++ [1]^^top ++ wt)%list)
    by (rewrite lpow_app_assoc; reflexivity).
  reflexivity.
Qed.

(** The two-close composition: H closes (gap 3+bH, run top), j1 grows,
    the next symbol D ALSO closes (gap 3+bD, run 2*j1+2 -- i.e. NOT top,
    since it grew), j2 more grow, and the walk lands on r2. Built as two
    back-to-back phase1_closed1 hops: entries stack shallowest-last-closed
    (D's entry sits on top of H's).
    Orbit instances (chunkstep-cases.json phase1:closed=2, all replayed):
      j1=2,j2=1: {top:2,stack:[],H:4,W:[1,1,9,1,5],p:80,L:512}
        -> {top:4,stack:[[8,6],[3,2]],H:5,W:[],p:80,L:512}, n=5
      j1=2,j2=1: {top:2,stack:[],H:8,W:[1,1,9,1,5],p:16,L:768}
        -> {top:4,stack:[[8,6],[7,2]],H:5,W:[],p:16,L:768}, n=5
      j1=2,j2=0, nonempty wt: {top:2,stack:[[3,2]],H:4,W:[1,1,9,5],p:392,L:104}
        -> {top:2,stack:[[8,6],[3,2],[3,2]],H:5,W:[],p:392,L:104}, n=4 *)
Lemma phase1_closed2 : forall top wt bH j1 bD j2 r2 rest,
  mrun (S j1 + S j2)
    (MC ([1]^^top ++ wt)
        (cons (S (S (S (S bH))))
              (prep j1 (cons (S (S (S (S bD)))) (prep j2 (cons r2 rest)))))) =
  Some (MC ([1]^^(2 * j2 + 2) ++ [0]^^(S (S (S bD))) ++
            [1]^^(2 * j1 + 2) ++ [0]^^(S (S (S bH))) ++ [1]^^top ++ wt)
           (cons r2 rest)).
Proof.
  introv.
  rewrite mrun_app.
  rewrite (phase1_closed1 top wt bH j1 (S (S (S (S bD)))) (prep j2 (cons r2 rest))).
  cbv iota.
  apply (phase1_closed1 (2 * j1 + 2) ([0]^^(S (S (S bH))) ++ [1]^^top ++ wt) bD j2 r2 rest).
Qed.

Print Assumptions phase1_closed1.
Print Assumptions phase1_closed2.

(** Composed hop lemmas for digitBirth2:term and digitBirth2:cascade
    (tools/chunkstep-cases.json), built from ParityHops2.v's
    exc_gap2x2_run_even (the four-level capped-carry collapse) generalized
    over an arbitrary count `k` of trailing (2,2) stack entries -- the
    `blocks k` wrapper Parity.v's own chunking machinery (exc_blocks,
    iter4_head) already provides -- composed with the bury + lapA
    skeleton chunkBig_w/chunkCascade_w use (git show
    HEAD:coq/ParityCasesA.v). Every instance below was replayed against
    mmirror.mjs (a literal JS transcription of exc/mstep) before encoding;
    n = 2*p+7 held in every digitBirth2:term/:cascade replay (7 + 4
    instances respectively, p in {0,2,4,6,20,22,52,54,84}, i in {0,1},
    k in {0,1,2}), matching the predecessor's recovered formula exactly
    (its p_coq is this file's p: F.p = p+2). One replay (gap=4, below the
    gap>=6 floor) deliberately falls OUTSIDE :cascade's precondition and
    needs 2 extra steps with a different landing shape, confirming that
    side condition is load-bearing, not conservative padding. *)

(** The exc-level landing for k trailing (2,2) pairs then nothing further
    (digitBirth2:term's shape): exc_blocks/iter4_head turn the k pairs
    into a +4k on the fresh head, the same digit-4-birth arithmetic
    exc_gap2x2_run_even's own nil case uses at k=0. *)
Lemma exc_gap2x2_run_even_term : forall J i k x,
  exc ([1]^^(2*J+4) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k nil) false (cons x nil) =
  ExC (cons 1 (cons 1 nil)) (cons (4*k+4) (prep i (cons 9 (prep J (cons (S x) nil))))).
Proof.
  introv.
  rewrite (exc_gap2x2_run_even J i (blocks k nil) x).
  rewrite exc_blocks.
  cbn [prep].
  rewrite iter4_head.
  cbn [exc push3].
  do 2 f_equal. lia.
Qed.

(** mstep-level closure: the run is followed only by k trailing pairs,
    then blank. Reproduced live at {top:2,stack:[[2,4]],H:4,W:[],p:2,
    L:10} (J=0,i=0,k=0, L=14 at this call, mstep call 7 of 7, landing
    rs=[4;9;18]) and {top:2,stack:[[2,4],[2,2]],H:4,W:[],p:2,L:10}
    (J=0,i=0,k=1, L=14, landing rs=[8;9;18], also call 7 of 7). *)
Lemma mstep_gap2x2_run_even_term : forall J i k L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*J+5) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k nil) (cons L nil)) =
  Some (MC (cons 1 (cons 1 nil))
           (cons (4*k+4) (prep i (cons 9 (prep J (cons (4 + L) nil)))))).
Proof.
  introv HL.
  replace (([1]^^(2*J+5) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k nil)%list)
    with ((cons 1 ([1]^^(2*J+4) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k nil))%list)
    by (replace (2*J+5) with (S (2*J+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_gap2x2_run_even_term J i k (3 + L)).
  reflexivity.
Qed.

(** Pump prefix to the term mechanism: entry state wall top 3 (post-lapA),
    prefix S n. Mirrors lapI_exit's own pump-then-fill shape exactly,
    landing mechanism swapped for mstep_gap2x2_run_even_term. *)
Lemma lapExit_gap2x2_term : forall n i k L,
  Nat.even L = true ->
  mrun (S n + 1)
    (MC (cons 1 (cons 1 (cons 1 ([0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k nil))))
        (prep (S n) (cons L nil))) =
  Some (MC (cons 1 (cons 1 nil))
           (cons (4*k+4) (prep i (cons 9 (prep n (cons (4 + L) nil)))))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite mrun_pump.
  rewrite wpump_lpow.
  cbn [mrun].
  replace (([1]^^(2 * S n)
            ++ cons 1 (cons 1 (cons 1 ([0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k nil))))%list)
    with (([1]^^(2 * n + 5) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k nil)%list)
    by (replace (2 * n + 5) with (2 * S n + 3) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_gap2x2_run_even_term n i k L HL).
  reflexivity.
Qed.

(** ** digitBirth2:term, the composed hop.

    F.top=2, F.H=4, F.stack = (gap=2,run=2i+4) then k trailing (2,2)
    pairs then nothing: bury (F.H=4 is exactly the b=0 case) + lapA +
    lapExit_gap2x2_term, mirroring chunkCascade's bury+lapA skeleton
    (git show HEAD:coq/ParityCasesA.v) verbatim. n = 2*p+7 (p = F.p-2),
    matching the predecessor's recovered formula on all replayed
    instances: p=0,i=0,k=0 (n=7); p=2,i=0,k=0 (n=11); p=4,i=1,k=0
    (n=15); p=0,i=0,k=1 (n=7); p=22,i=1,k=0 (n=51, JSON ex1); p=6,i=1,
    k=1 (n=19, JSON ex2); p=84,i=0,k=0 (n=175, JSON ex3). *)
Lemma digitBirth2_term : forall i k p L,
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 ([0;0] ++ [1]^^(2*i+4) ++ blocks k nil)))
        (cons 4 (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 nil))
           (cons (4*k+4) (prep i (cons 9 (prep p (cons (8 + L) nil)))))).
Proof.
  introv HL.
  cbn [mrun].
  change 4 with (S (S (S (S 0)))).
  rewrite mstep_bury by apply prep_ne.
  rewrite mrun_app.
  replace (([0]^^(S (S (S 0))) ++ cons 1 (cons 1 ([0;0] ++ [1]^^(2*i+4) ++ blocks k nil)))%list)
    with ((cons 0 (cons 0 (cons 0 (cons 1 (cons 1 ([0;0] ++ [1]^^(2*i+4) ++ blocks k nil))))))%list)
    by reflexivity.
  rewrite (lapA (S p) _ L HL).
  change (mrun (S p + 1)
      (MC (cons 1 (cons 1 (cons 1 ([0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k nil))))
          (prep (S p) (cons (S (3 + L)) nil))) =
    Some (MC (cons 1 (cons 1 nil))
             (cons (4*k+4) (prep i (cons 9 (prep p (cons (8 + L) nil))))))).
  rewrite (lapExit_gap2x2_term p i k (S (3 + L)))
    by (replace (S (3 + L)) with (S (S (S (S L)))) by lia;
        cbn [Nat.even]; assumption).
  reflexivity.
Qed.

Print Assumptions exc_gap2x2_run_even_term.
Print Assumptions mstep_gap2x2_run_even_term.
Print Assumptions lapExit_gap2x2_term.
Print Assumptions digitBirth2_term.

(** ** digitBirth2:cascade: the same shape, with a further (gap=4+g,
    run+deeper=tail) entry after the k trailing pairs instead of blank.
    gap>=6 (g>=2) is load-bearing: with g=0 (gap=4 exactly) the excursion
    doesn't stop at this entry -- it walks INTO its run (an
    mstep_gap2_run_odd-shaped continuation when that run is odd, more
    steps, a different landing), replayed at {top:2,stack:[[2,6],[4,3]],
    H:4,W:[],p:2,L:10} (n=9, not the n=7 the p=0 formula would predict,
    landing stack=[[3,5]] -- the run MERGES with the exit, it doesn't
    stay a separate entry). Not proven for g=0; digitBirth2_cascade below
    requires g explicit (gap = 4+g, matching the JSON's own examples,
    which never go below gap=6, i.e. g=2). *)
Lemma exc_gap2x2_run_even_cascade : forall J i k g tail x,
  exc ([1]^^(2*J+4) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail)) false (cons x nil) =
  ExC (cons 1 (cons 1 ([0]^^g ++ tail)))
      (cons (4*k+4) (prep i (cons 9 (prep J (cons (S x) nil))))).
Proof.
  introv.
  rewrite (exc_gap2x2_run_even J i (blocks k ([0]^^(4+g) ++ tail)) x).
  rewrite exc_blocks.
  cbn [prep].
  rewrite iter4_head.
  replace (([0]^^(4+g) ++ tail)%list)
    with ((cons 0 (cons 0 (cons 0 (cons 0 ([0]^^g ++ tail)))))%list)
    by (replace (4+g) with (S (S (S (S g)))) by lia; reflexivity).
  cbn [exc push3].
  do 2 f_equal. lia.
Qed.

(** mstep-level closure. Reproduced live:
    {top:2,stack:[[2,4],[6,2]],H:4,W:[],p:54,L:196} (J=0,i=0,k=0,g=2,
    tail=[1;1], L=200 at this call, landing rs=[4;9;(52 ones);204]);
    {top:2,stack:[[2,4],[2,2],[6,2]],H:4,W:[],p:6,L:388} (J=0,i=0,k=1,
    g=2, landing H'=8); {top:2,stack:[[2,4],[2,2],[2,2],[8,5]],H:4,
    W:[],p:4,L:10} (J=0,i=0,k=2,g=4,tail=[1;1;1;1;1], landing
    stack'=[[4,5]], H'=12) -- all exact n=2p+7 and endpoint matches. *)
Lemma mstep_gap2x2_run_even_cascade : forall J i k g tail L,
  Nat.even L = true ->
  mstep (MC ([1]^^(2*J+5) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail)) (cons L nil)) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ tail)))
           (cons (4*k+4) (prep i (cons 9 (prep J (cons (4 + L) nil)))))).
Proof.
  introv HL.
  replace (([1]^^(2*J+5) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail))%list)
    with ((cons 1 ([1]^^(2*J+4) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail)))%list)
    by (replace (2*J+5) with (S (2*J+4)) by lia; reflexivity).
  cbn [mstep].
  rewrite HL.
  rewrite (exc_gap2x2_run_even_cascade J i k g tail (3 + L)).
  reflexivity.
Qed.

Lemma lapExit_gap2x2_cascade : forall n i k g tail L,
  Nat.even L = true ->
  mrun (S n + 1)
    (MC (cons 1 (cons 1 (cons 1 ([0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail)))))
        (prep (S n) (cons L nil))) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ tail)))
           (cons (4*k+4) (prep i (cons 9 (prep n (cons (4 + L) nil)))))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite mrun_pump.
  rewrite wpump_lpow.
  cbn [mrun].
  replace (([1]^^(2 * S n)
            ++ cons 1 (cons 1 (cons 1 ([0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail)))))%list)
    with (([1]^^(2 * n + 5) ++ [0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail))%list)
    by (replace (2 * n + 5) with (2 * S n + 3) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_gap2x2_run_even_cascade n i k g tail L HL).
  reflexivity.
Qed.

(** ** digitBirth2:cascade, the composed hop. Same bury+lapA skeleton as
    digitBirth2_term, landing mechanism swapped for the deeper-entry
    closure. p=54,i=0,k=0,g=2 (n=111); p=22,i=0,k=0,g=6 (n=47);
    p=6,i=0,k=1,g=2 (n=15); p=4,i=0,k=2,g=4 (n=11): all JSON/hand
    instances above, n = 2*p+7 throughout. *)
Lemma digitBirth2_cascade : forall i k g tail p L,
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 ([0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail))))
        (cons 4 (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 ([0]^^g ++ tail)))
           (cons (4*k+4) (prep i (cons 9 (prep p (cons (8 + L) nil)))))).
Proof.
  introv HL.
  cbn [mrun].
  change 4 with (S (S (S (S 0)))).
  rewrite mstep_bury by apply prep_ne.
  rewrite mrun_app.
  replace (([0]^^(S (S (S 0))) ++ cons 1 (cons 1 ([0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail))))%list)
    with ((cons 0 (cons 0 (cons 0 (cons 1 (cons 1 ([0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail)))))))%list)
    by reflexivity.
  rewrite (lapA (S p) _ L HL).
  change (mrun (S p + 1)
      (MC (cons 1 (cons 1 (cons 1 ([0;0;1;1;0;0] ++ [1]^^(2*i+4) ++ blocks k ([0]^^(4+g) ++ tail)))))
          (prep (S p) (cons (S (3 + L)) nil))) =
    Some (MC (cons 1 (cons 1 ([0]^^g ++ tail)))
             (cons (4*k+4) (prep i (cons 9 (prep p (cons (8 + L) nil))))))).
  rewrite (lapExit_gap2x2_cascade p i k g tail (S (3 + L)))
    by (replace (S (3 + L)) with (S (S (S (S L)))) by lia;
        cbn [Nat.even]; assumption).
  reflexivity.
Qed.

Print Assumptions exc_gap2x2_run_even_cascade.
Print Assumptions mstep_gap2x2_run_even_cascade.
Print Assumptions lapExit_gap2x2_cascade.
Print Assumptions digitBirth2_cascade.

(** ** C:shift1: the triple-lap chain.

    Traced live at {top:2,stack:[[3,2]],H:5,W:[],p:6,L:4} (34 mstep
    calls) and confirmed to decompose into exactly THREE rounds of the
    SAME bury+lapA+exit skeleton digitBirth2_term/cascade use, plus one
    B-pop bridge: round 1 (calls 1-15, landing rs=[4;1;1;1;1;12]) and
    round 3 (calls 28-34, the final boundary) both fire
    mstep_insulate_gap3 (ParityHops.v); round 2 (calls 16-26, landing in
    B-mode) fires mstep_gap2_run_odd (ParityHops2.v, call 26 exactly:
    j=2,i=1,wt=[0;0;1;1],L=16). Each round costs 2*p_round+7 steps where
    p_round is F.p minus 2,4,6 respectively (F.p-6 must stay a nat: the
    F.p>=6 side condition), so the total is (2(p+4)+7)+(2(p+2)+7)+1+
    (2p+7) = 6p+34 raw calls for p = F.p-6 -- matching n=6*F.p-2
    (p=6->34, p=8->46, p=10->58, p=100->598, all replayed) and the
    JSON's flat "p'=p-6, L'=L+24" exactly (the flatness is an ARTIFACT
    of 3 fixed rounds, not a shortcut -- step count still scales with
    p). Confirmed with a nontrivial deeper stack too: JSON's own example
    1 (deeper=[[3,7],[7,2]], p=416) replays to n=2494=6*416-2 and lands
    exactly at the JSON's stated after-state; deeper passes through
    every round untouched, never inspected. *)

(** Round type 1/3: H=5 buries (b=1, gap=4), lapA, pump to
    mstep_insulate_gap3. General in the wall past its own leading 1 (so
    it composes into itself for round 3, and into chunk_gap2_odd for
    round 2): the landing wall is the input wall with one more 1 glued
    on front, one gap-cell shallower down at the mstep_insulate_gap3
    call, then re-closed by the caller. *)
Lemma lapExit_gap3 : forall n rest2 L,
  Nat.even L = true ->
  mrun (S n + 1)
    (MC (cons 1 (cons 1 (cons 1 ([0;0;0] ++ cons 1 rest2))))
        (prep (S n) (cons L nil))) =
  Some (MC (cons 1 (cons 1 rest2))
           (cons 4 (prep n (cons (4 + L) nil)))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite mrun_pump.
  rewrite wpump_lpow.
  cbn [mrun].
  replace (([1]^^(2 * S n) ++ cons 1 (cons 1 (cons 1 ([0;0;0] ++ cons 1 rest2))))%list)
    with (([1]^^(2 * n + 5) ++ [0;0;0] ++ cons 1 rest2)%list)
    by (replace (2 * n + 5) with (2 * S n + 3) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_insulate_gap3 n rest2 L HL).
  reflexivity.
Qed.

Lemma chunk_gap3 : forall tailW p L,
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 tailW)
        (cons 5 (prep (S (S p)) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 tailW))
           (cons 4 (prep p (cons (8 + L) nil)))).
Proof.
  introv HL.
  cbn [mrun].
  change 5 with (S (S (S (S (S 0))))).
  rewrite mstep_bury by apply prep_ne.
  rewrite mrun_app.
  replace (([0]^^(S (S (S (S 0)))) ++ cons 1 tailW)%list)
    with ((cons 0 (cons 0 (cons 0 (cons 0 (cons 1 tailW)))))%list)
    by reflexivity.
  rewrite (lapA (S p) _ L HL).
  change (mrun (S p + 1)
      (MC (cons 1 (cons 1 (cons 1 ([0;0;0] ++ cons 1 tailW))))
          (prep (S p) (cons (S (3 + L)) nil))) =
    Some (MC (cons 1 (cons 1 tailW))
             (cons 4 (prep p (cons (8 + L) nil))))).
  rewrite (lapExit_gap3 p tailW (S (3 + L)))
    by (replace (S (3 + L)) with (S (S (S (S L)))) by lia;
        cbn [Nat.even]; assumption).
  reflexivity.
Qed.

Print Assumptions lapExit_gap3.
Print Assumptions chunk_gap3.

(** Round type 2: H=4 buries (b=0, gap=3), lapA, pump to
    mstep_gap2_run_odd -- the odd-run partial exit, landing in B-mode.
    `deeper` is everything past the wall this round's own bury+lapA
    manufacture; the fixed 10-cell prefix is round 1's own leftover
    (gap3,run2,gap3 -- F0's buried top glued to F0's own stack entry)
    re-exposed one layer down, matching call 26's traced j=2,i=1
    exactly at p_round=2 (F.p=6). *)
Lemma lapExit_gap2_odd : forall n deeper L,
  Nat.even L = true ->
  mrun (S n + 1)
    (MC (cons 1 (cons 1 (cons 1 ([0;0;1;1;1;0;0;0;1;1] ++ deeper))))
        (prep (S n) (cons L nil))) =
  Some (MB (cons 1 ([0;0;1;1] ++ deeper))
           (prep 1 (cons 5 (prep n (cons (4 + L) nil))))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite mrun_pump.
  rewrite wpump_lpow.
  cbn [mrun].
  replace (([1]^^(2 * S n) ++ cons 1 (cons 1 (cons 1 ([0;0;1;1;1;0;0;0;1;1] ++ deeper))))%list)
    with (([1]^^(2 * n + 5) ++ [0;0] ++ [1]^^(2*1+1) ++ cons 0 ([0;0;1;1] ++ deeper))%list)
    by (replace (2 * n + 5) with (2 * S n + 3) by lia;
        rewrite lpow_app_assoc; reflexivity).
  rewrite (mstep_gap2_run_odd n 1 ([0;0;1;1] ++ deeper) L HL).
  reflexivity.
Qed.

Lemma chunk_gap2_odd : forall deeper p L,
  Nat.even L = true ->
  mrun (S ((S (S p) + 2) + (S p + 1)))
    (MC (cons 1 (cons 1 (cons 1 ([0;0;0;1;1] ++ deeper))))
        (cons 4 (prep (S (S p)) (cons L nil)))) =
  Some (MB (cons 1 ([0;0;1;1] ++ deeper))
           (prep 1 (cons 5 (prep p (cons (8 + L) nil))))).
Proof.
  introv HL.
  cbn [mrun].
  change 4 with (S (S (S (S 0)))).
  rewrite mstep_bury by apply prep_ne.
  rewrite mrun_app.
  replace (([0]^^(S (S (S 0))) ++ cons 1 (cons 1 (cons 1 ([0;0;0;1;1] ++ deeper))))%list)
    with ((cons 0 (cons 0 (cons 0 (cons 1 (cons 1 (cons 1 ([0;0;0;1;1] ++ deeper)))))))%list)
    by reflexivity.
  rewrite (lapA (S p) _ L HL).
  change (mrun (S p + 1)
      (MC (cons 1 (cons 1 (cons 1 ([0;0;1;1;1;0;0;0;1;1] ++ deeper))))
          (prep (S p) (cons (S (3 + L)) nil))) =
    Some (MB (cons 1 ([0;0;1;1] ++ deeper))
             (prep 1 (cons 5 (prep p (cons (8 + L) nil)))))).
  rewrite (lapExit_gap2_odd p deeper (S (3 + L)))
    by (replace (S (3 + L)) with (S (S (S (S L)))) by lia;
        cbn [Nat.even]; assumption).
  reflexivity.
Qed.

Print Assumptions lapExit_gap2_odd.
Print Assumptions chunk_gap2_odd.

(** The B-pop bridge between round 2 and round 3: a direct unfold of
    mstep's own MB clause at a=1 (round 2's B-mode landing always pops a
    literal 1, never a general a -- traced at call 27). *)
Lemma mstep_bpop1 : forall (ws : list Sym) (rest : list nat),
  mstep (MB ws (cons (S O) rest)) = Some (MC (cons 1 (cons 1 ws)) rest).
Proof. introv. reflexivity. Qed.

Print Assumptions mstep_bpop1.

(** ** C:shift1, the full composed hop: chunk_gap3 (round 1, p+4) ;
    chunk_gap2_odd (round 2, p+2) ; mstep_bpop1 (bridge) ;
    chunk_gap3 (round 3, p). F.p = p+6 (the side condition, p:nat makes
    F.p>=6 structural). *)
Lemma C_shift1 : forall deeper p L,
  Nat.even L = true ->
  mrun (S ((S (S (S (S (S (S p))))) + 2) + (S (S (S (S (S p)))) + 1))
        + (S ((S (S (S (S p))) + 2) + (S (S (S p)) + 1))
           + (1 + S ((S (S p) + 2) + (S p + 1)))))
    (MC (cons 1 (cons 1 (cons 0 (cons 0 (cons 0 (cons 1 (cons 1 deeper)))))))
        (cons 5 (prep (S (S (S (S (S (S p)))))) (cons L nil)))) =
  Some (MC (cons 1 (cons 1 (cons 1 (cons 1 (cons 0 (cons 0 (cons 1 (cons 1 deeper))))))))
           (cons 4 (prep p (cons (24 + L) nil)))).
Proof.
  introv HL.
  rewrite mrun_app.
  rewrite (chunk_gap3 (cons 1 (cons 0 (cons 0 (cons 0 (cons 1 (cons 1 deeper)))))) (S (S (S (S p)))) L HL).
  change (mrun (S ((S (S (S (S p))) + 2) + (S (S (S p)) + 1))
              + (1 + S ((S (S p) + 2) + (S p + 1))))
      (MC (cons 1 (cons 1 (cons 1 ([0;0;0;1;1] ++ deeper))))
          (cons 4 (prep (S (S (S (S p)))) (cons (8 + L) nil)))) =
    Some (MC (cons 1 (cons 1 (cons 1 (cons 1 (cons 0 (cons 0 (cons 1 (cons 1 deeper))))))))
             (cons 4 (prep p (cons (24 + L) nil))))).
  assert (HL8 : Nat.even (8 + L) = true).
  { replace (8 + L) with (S (S (S (S (S (S (S (S L)))))))) by lia.
    cbn [Nat.even]. exact HL. }
  rewrite mrun_app.
  rewrite (chunk_gap2_odd deeper (S (S p)) (8 + L) HL8).
  change (mrun (1 + S ((S (S p) + 2) + (S p + 1)))
      (MB (cons 1 ([0;0;1;1] ++ deeper))
          (prep 1 (cons 5 (prep (S (S p)) (cons (16 + L) nil))))) =
    Some (MC (cons 1 (cons 1 (cons 1 (cons 1 (cons 0 (cons 0 (cons 1 (cons 1 deeper))))))))
             (cons 4 (prep p (cons (24 + L) nil))))).
  rewrite mrun_app.
  cbn [mrun prep].
  rewrite mstep_bpop1.
  change (mrun (S ((S (S p) + 2) + (S p + 1)))
      (MC (cons 1 (cons 1 (cons 1 ([0;0;1;1] ++ deeper))))
          (cons 5 (prep (S (S p)) (cons (16 + L) nil)))) =
    Some (MC (cons 1 (cons 1 (cons 1 (cons 1 (cons 0 (cons 0 (cons 1 (cons 1 deeper))))))))
             (cons 4 (prep p (cons (24 + L) nil))))).
  assert (HL16 : Nat.even (16 + L) = true).
  { replace (16 + L) with (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (L)))))))))))))))))
      by lia.
    cbn [Nat.even]. exact HL. }
  rewrite (chunk_gap3 (cons 1 (cons 1 ([0;0;1;1] ++ deeper))) p (16 + L) HL16).
  replace (8 + (16 + L)) with (24 + L) by lia.
  reflexivity.
Qed.

Print Assumptions C_shift1.
