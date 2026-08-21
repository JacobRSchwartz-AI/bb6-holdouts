From BusyCoq Require Import Individual62.
From BusyCoq Require Import Parity.
From BusyCoq Require Import ParityHops.
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
