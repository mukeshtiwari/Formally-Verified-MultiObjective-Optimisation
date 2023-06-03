Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.manger_sets.
Require Import CAS.coq.eqv.reduce
  CAS.coq.uop.commutative_composition
  CAS.coq.uop.properties.

Require Import CAS.coq.sg.properties
  CAS.coq.sg.product.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.reduce. 

(* for testing *)
Require Import CAS.coq.sg.manger_llex.
Require Import CAS.coq.eqv.nat. 
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.po.from_sg.
Import ListNotations.


Section Computation.


(* 
  A = type of active component
  P = type of passive component
*)   

(* replace bSAP with this one *)

Definition manger_product_phase_0
           {A P : Type}
           (eqA : brel A)
           (eqP : brel P)                       
           (mulA : binary_op A)
           (mulP : binary_op P) : binary_op (finite_set (A * P)) := 
  bop_lift (brel_product eqA eqP) (bop_product mulA mulP). 

  

Definition bop_manger_product 
    {A P : Type}
    (eqA lteA : brel A)
    (eqP : brel P)            
    (addP : binary_op P)
    (mulA : binary_op A)
    (mulP : binary_op P) : binary_op (finite_set (A * P)) :=
    bop_reduce (@uop_manger A P eqA lteA addP) 
      (manger_product_phase_0 eqA eqP mulA mulP).


End Computation.



(* 
Section Testing.

(*  A = nat * nat, P = nat *) 
   
Local Definition eqA := brel_product brel_eq_nat brel_eq_nat. 
Local Definition addA := bop_product bop_min bop_min. 
Local Definition lteA := brel_lte_left eqA addA. 
Local Definition mulA := bop_product bop_plus bop_plus. 

Local Definition eqP  := brel_eq_nat.
Local Definition addP := bop_min. 
Local Definition mulP := bop_plus.

Local Definition manger_add := @bop_manger _ _ eqA lteA eqP addP.
Local Definition manger_mul := bop_manger_product eqA lteA eqP addP mulA mulP.
(*
  Check manger_add.
  : binary_op (finite_set (nat * nat * nat))

  Check manger_mul.
  : binary_op (finite_set (nat * nat * nat))
 *)

Open Scope nat_scope. 

Local Definition s1 := ((1, 2), 8) :: nil.
Local Definition s2 := ((3, 5), 9) :: nil.
Local Definition s3 := ((0, 5), 9) :: nil.
Local Definition s4 := ((1, 2), 10) :: nil.
Local Definition s5 := ((1, 2), 1):: ((1, 2), 2)::((1, 2), 3) :: nil.
Compute (manger_add s1 s2). (* = (1, 2, 8) :: nil *)
Compute (manger_add s1 s3). (* = (0, 5, 9) :: (1, 2, 8) :: nil *)
Compute (manger_add s1 s4). (* = (1, 2, 8) :: nil *)
Compute (manger_add s1 s1). (* = (1, 2, 8) :: nil *)
Compute (manger_add s5 nil). (* = (1, 2, 1) :: nil *)
Compute (manger_add nil s5). (* = (1, 2, 1) :: nil *)
Compute (manger_mul s1 s2). (* = (4, 7, 17) :: nil *) 
Compute (manger_mul s2 s5). (* = (4, 7, 10) :: nil *)
Compute (manger_add (manger_mul s5 s1) (manger_mul s5 s3)). (* (1, 7, 10) :: (2, 4, 9) :: nil *) 
Compute (manger_mul s5 (manger_add s1 s3)).                 (* (2, 4, 9) :: (1, 7, 10) :: nil *) 

End Testing.
*)

Section Theory.

Variables  
  (A P : Type)
  (zeroP : P) (* 0 *)
  (eqA lteA : brel A)
  (eqP : brel P)            
  (addP : binary_op P)
  (wA : A)
  (wP : P) 
  (fA : A -> A) 
  (ntA : brel_not_trivial A eqA fA)
  (conA : brel_congruence A eqA eqA) 
  (mulA : binary_op A)
  (mulP : binary_op P)
  (refA : brel_reflexive A eqA)
  (symA : brel_symmetric A eqA)
  (trnA : brel_transitive A eqA)
  (refP : brel_reflexive P eqP)
  (symP : brel_symmetric P eqP)
  (trnP : brel_transitive P eqP)
  (ntot : properties.brel_not_total A lteA)
  (conP : brel_congruence P eqP eqP)
  (cong_addP : bop_congruence P eqP addP) 
  (conLte : brel_congruence A eqA lteA) 
  (refLte : brel_reflexive A lteA)
  (trnLte : brel_transitive A lteA) 
  (addP_assoc : bop_associative P eqP addP)
  (addP_com : bop_commutative P eqP addP)
  (idemP : bop_idempotent P eqP addP)
  (zeropLid : ∀ (p : P), eqP (addP zeroP p) p = true)
  (zeropRid : ∀ (p : P), eqP (addP p zeroP) p = true).

(* Assumption about mulA and mulP  *)
Variables 
  (mulA_assoc : bop_associative A eqA mulA)
  (mulP_assoc : bop_associative P eqP mulP)
  (mulA_comm : bop_commutative A eqA mulA)
  (mulP_comm : bop_commutative P eqP mulP)
  (cong_mulA : bop_congruence A eqA mulA)
  (cong_mulP : bop_congruence P eqP mulP).

Local Notation "[EQP0]" :=  (brel_set (brel_product eqA eqP)) (only parsing).
Local Notation "[EQP1]" :=  (equal_manger_phase_1 eqA eqP addP) (only parsing). 
Local Notation "[MP1]" :=  (uop_manger_phase_1 eqA addP) (only parsing).
Local Notation "[MPP0]" :=  (manger_product_phase_0 eqA eqP mulA mulP) (only parsing).
Local Notation "[MP]" := (bop_manger_product eqA lteA eqP addP mulA mulP) (only parsing). 
Local Notation "[MR]" := (@uop_manger_phase_2 A P lteA) (only parsing).
Local Notation "[EQ]" := (equal_manger eqA lteA eqP addP) (only parsing).


(* Begin Admit *)      

(*
  X := [(a, b); (c, d); (a, e)]
  Y := [(u, v); (x, y); (x, t)]

  1. (uop_manger_phase_1 eqA addP X) =  
    [(a, b + e); (c, d)]
  
  2. (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP X) Y) = 
  [
    (mulA a u, mulP (b + e) v); 
    (mulA a x, mulP (b + e) y;
    (mulA a x, mulP (b + e) t);
    (mulA c u, mulP d v);
    (mulA c x, mulP d y);
    (mulA c x, mulP d t);
  ]

  3. (manger_product_phase_0 eqA eqP mulA mulP X Y) = 
  [
    (mulA a u, mulP b v);
    (mulA a x, mulP b y);
    (mulA a x, mulP b t);
    (mulA c u, mulP d v);
    (mulA c x, mulP d y);
    (mulA c x, mulP d t);
    (mulA a u, mulP e v);
    (mulA a x, mulP e y);
    (mulA a x, mulP e t)
  ]

  Now, let's say I want to filter (mulA a x) from 
  equation 3 and 2. 
  2 gives me:
  [
    (mulA a x, mulP (b + e) y;
    (mulA a x, mulP (b + e) t);
  ]
  and 3 gives me:
  [
    (mulA a x, mulP b y);
    (mulA a x, mulP b t);
    (mulA a x, mulP e y);
    (mulA a x, mulP e t)
  ]

  (* addP is + *)
  mulP needs to distribute over addP 
  Prove that:
  mulP (b + e) y + mulP (b + e) t = 
  mulP b y + mulP b t + mulP e y + 
  mulP e t 

*)

Lemma addP_gen_idempotent : 
  ∀ x y : P, 
  eqP x y = true → eqP (addP x y) y = true.
Proof. 
  intros * Ha.
  assert (Hb := cong_addP _ _ _ _ Ha (refP y)).
  assert (Hc := idemP y).
  exact (trnP _ _ _ Hb Hc).
Qed. 

Local Notation "x =S= y" := (manger_llex.eqSAP x y = true) (at level 70,
  only parsing).

Lemma bProp_cong : 
  forall au,
  theory.bProp_congruence (A * P) (brel_product eqA eqP)
  (λ '(x, _), eqA x au).
Proof.
  intros * (ax, bx) (aw, bw) Ha;
  cbn in Ha.
  eapply Bool.andb_true_iff in Ha.
  destruct Ha as (Hal & Har).
  case_eq (eqA ax au);
  case_eq (eqA aw au);
  intros Hb Hc; try reflexivity.
  rewrite (trnA _ _ _ (symA _ _ Hal) Hc) in 
  Hb; congruence.
  rewrite (trnA _ _ _ Hal Hb) in Hc;
  congruence.
Qed.

Lemma bop_cong : 
  bop_congruence (A * P) (brel_product eqA eqP) (bop_product mulA mulP).
Proof.
  eapply bop_product_congruence; assumption.
Qed.
    

Lemma bop_assoc : 
  bop_associative (A * P) (manger_llex.eqAP A P eqA eqP)
  (bop_product mulA mulP).
Proof.
  eapply bop_product_associative; assumption.
Qed.


(* It's good idea to create a hint database and 
  writing some custom tactics using coq-elpi *)
Lemma brel_set_manger_product_phase_0_dist : 
  forall (X Y U : finite_set (A * P)),
  brel_set (brel_product eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP (X ++ Y) U)
  (manger_product_phase_0 eqA eqP mulA mulP X U ++
   manger_product_phase_0 eqA eqP mulA mulP Y U) = true.
Proof.
  intros *.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, ay) Ha]; try assumption.
  +
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption;
    destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
    (* Now replace *)
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (xa, xp) (ya, yp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric |
    ]; try assumption.
    (* case analysis on Ha *)
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha].
    ++
      (* go left *)
      eapply set.in_set_concat_intro; left.
      eapply in_set_bop_lift_intro;
      [eapply refAP | eapply trnAP | eapply symAP | eapply 
      bop_cong | exact Ha | exact Hb];
      try assumption.
    ++
      (* go right *)
      eapply set.in_set_concat_intro; right.
      eapply in_set_bop_lift_intro;
      [eapply refAP | eapply trnAP | eapply symAP | eapply 
      bop_cong | exact Ha | exact Hb]; 
      try assumption.
  +
    (* I need find out (xa, xp) (ya, yp) such 
    that ax = mulA xa ya & ay = mulP xp yp from Ha *) 

    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    (* case analysis on Ha*)
    destruct Ha as [Ha | Ha].
    ++
      eapply in_set_bop_lift_elim in Ha;   
      [| eapply refAP | eapply symAP]; try assumption;
      destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
      eapply in_set_bop_lift_intro_v2;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | eapply set.in_set_concat_intro; left; 
      exact Ha | exact Hb | ]; try assumption.
    ++
       eapply in_set_bop_lift_elim in Ha;   
      [| eapply refAP | eapply symAP]; try assumption;
      destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
      eapply in_set_bop_lift_intro_v2;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | eapply set.in_set_concat_intro; right; 
      exact Ha | exact Hb | ]; try assumption.
Qed.

      

Lemma brel_set_manger_product_phase_0_comm : 
  forall (X Y U : finite_set (A * P)),
  brel_set (brel_product eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP (X ++ Y) U)
  (manger_product_phase_0 eqA eqP mulA mulP (Y ++ X) U) = true.
Proof.
  intros *.
  eapply brel_set_transitive;
  [eapply refAP | eapply symAP | eapply trnAP | 
  eapply brel_set_manger_product_phase_0_dist | 
  eapply brel_set_symmetric]; 
  try assumption.
  eapply brel_set_transitive;
  [eapply refAP | eapply symAP | eapply trnAP | 
  eapply brel_set_manger_product_phase_0_dist | 
  eapply brel_set_symmetric]; 
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (ax, bx) Ha];
  try assumption.
  +
    eapply set.in_set_concat_intro.
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha];
    [right | left]; assumption.
  +
    eapply set.in_set_concat_intro.
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha];
    [right | left]; assumption.
Qed.



Lemma brel_set_manger_product_phase_0_swap : 
  forall (X Y U : finite_set (A * P)) au bu,
  brel_set (brel_product eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP (((au, bu) :: X) ++ Y) U)
  (manger_product_phase_0 eqA eqP mulA mulP (X ++ (au, bu) :: Y) U) = true.
Proof.
  intros *.
  remember (((au, bu) :: X)) as Xa.
  remember ((au, bu) :: Y) as Ya.
  eapply brel_set_transitive;
  [eapply refAP | eapply symAP | eapply trnAP | 
  eapply brel_set_manger_product_phase_0_dist | 
  eapply brel_set_symmetric]; 
  try assumption.
  eapply brel_set_transitive;
  [eapply refAP | eapply symAP | eapply trnAP | 
  eapply brel_set_manger_product_phase_0_dist | 
  eapply brel_set_symmetric]; 
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (ax, bx) Ha];
  try assumption.
  +
    subst; cbn in Ha |- *.
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha].
    eapply union.in_set_uop_duplicate_elim_elim,
    set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha].
    ++
      (* go right; left *)
      eapply set.in_set_concat_intro; right;
      eapply union.in_set_dup_elim_intro;
      [eapply symAP | eapply trnAP | eapply 
      set.in_set_concat_intro; left]; try assumption.
    ++
      eapply set.in_set_concat_intro; left.
      unfold manger_product_phase_0, bop_lift.
      eapply union.in_set_dup_elim_intro;
      [eapply symAP | eapply trnAP | exact Ha];
      try assumption.
    ++
      eapply set.in_set_concat_intro; right;
      eapply union.in_set_dup_elim_intro;
      [eapply symAP | eapply trnAP | eapply 
      set.in_set_concat_intro; right]; try assumption.
      eapply union.in_set_uop_duplicate_elim_elim in Ha;
      try assumption.
  +
    (* other direction *)
    subst; 
    eapply set.in_set_concat_elim in Ha;
    [|eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha].
    ++
      eapply set.in_set_concat_intro; left;
      cbn; eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ]; try assumption.
      eapply set.in_set_concat_intro; right.
      unfold manger_product_phase_0 in Ha.
      eapply in_set_bop_lift_elim in Ha;
      [| eapply refAP | eapply symAP]; try assumption;
      destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
      eapply set.in_set_right_congruence with 
      (bop_product mulA mulP (xa, xp) (ya, yp));
      [eapply symAP | eapply trnAP | eapply brel_product_symmetric |
      ]; try assumption.
      eapply in_set_list_product_intro;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | exact Ha | exact Hb];
      try assumption.
    ++
      cbn in Ha |- *;
      eapply union.in_set_uop_duplicate_elim_elim,
      set.in_set_concat_elim in Ha;
      [| eapply symAP]; try assumption.
      destruct Ha as [Ha | Ha].
      +++
        eapply set.in_set_concat_intro; left;
        eapply union.in_set_uop_duplicate_elim_intro;
        [eapply symAP | eapply trnAP | ]; 
        try assumption.
        eapply set.in_set_concat_intro; left; 
        assumption.
      +++
        eapply set.in_set_concat_intro; right;
        eapply union.in_set_uop_duplicate_elim_intro;
        [eapply symAP | eapply trnAP | ]; 
        try assumption.
Qed.


(* requires commutativity *)
Lemma brel_set_manger_product_phase_0_swap_v1: 
  forall (X Y : finite_set (A * P)),
  brel_set (brel_product eqA eqP) 
  (manger_product_phase_0 eqA eqP mulA mulP X Y)
  (manger_product_phase_0 eqA eqP mulA mulP Y X) = true.
Proof.
  intros *;
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Ha];
  try assumption.
  +
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption;
    destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
    (* Now replace *)
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (xa, xp) (ya, yp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric |
    ]; try assumption.
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (ya, yp) (xa, xp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric | ];
    try assumption;
    [eapply brel_product_symmetric| ];
    try assumption.
    eapply brel_product_intro;
    [eapply mulA_comm | eapply mulP_comm].
    eapply in_set_bop_lift_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | exact Hb  | exact Ha];
    try assumption.
  +
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption;
    destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
    (* Now replace *)
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (xa, xp) (ya, yp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric |
    ]; try assumption.
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (ya, yp) (xa, xp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric | ];
    try assumption;
    [eapply brel_product_symmetric| ];
    try assumption. 
    eapply brel_product_intro;
    [eapply mulA_comm | eapply mulP_comm].
    eapply in_set_bop_lift_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | exact Hb  | exact Ha];
    try assumption.
Qed.


    


Lemma manger_product_phase_0_comm : 
  forall (X Y U : finite_set (A * P)) au ax bx,
  eqP 
    ((matrix_algorithms.sum_fn zeroP addP snd
      (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP
          (((ax, bx) :: X) ++ Y) U))))
    (matrix_algorithms.sum_fn zeroP addP snd
      (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP
          (X ++ ((ax, bx) :: Y)) U))) = true.
Proof.
  intros *.
  eapply sum_fn_congruence_general_set with 
  (eqA := eqA) (lteA := lteA) (fA := fA);
  try assumption.
  + eapply addP_gen_idempotent.
  +
    repeat rewrite  list_filter_lib_filter_same;
    eapply filter_congruence_gen; 
    try assumption; try (eapply bProp_cong).
    eapply brel_set_manger_product_phase_0_swap.
Qed.


Lemma manger_product_phase_0_dist : 
  forall (X Y U : finite_set (A * P)) au,
  eqP
  (matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP (X ++ Y) U)))
  (matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X U ++ 
        manger_product_phase_0 eqA eqP mulA mulP Y U))) = true.
Proof.
  intros *.
  eapply sum_fn_congruence_general_set with 
  (eqA := eqA) (lteA := lteA) (fA := fA);
  try assumption.
  + eapply addP_gen_idempotent.
  +
    repeat rewrite  list_filter_lib_filter_same;
    eapply filter_congruence_gen; 
    try assumption; try (eapply bProp_cong).
    eapply brel_set_manger_product_phase_0_dist.
Qed.
  


(* Begin admit *)


(* 
Mukesh: Tim, I ran out of energy for these admitted proofs, so 
may be you can discharge them when rewriting this file. 
There is already pen-and-paper proof for the below one, 
and others are trivial, I hope.
*)


Lemma manger_product_phase_0_manger_merge_interaction : 
  forall (Y U : finite_set (A * P)) au ax bx, 
  no_dup eqA (map fst Y) = true -> 
  eqP
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (manger_merge_sets_new eqA addP Y (ax, bx)) U)))
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP ((ax, bx) :: Y) U))) = true.
Proof.
  intros * Ha.

  (* Case analysis ax  ∈ Y ∨ ax ∉ Y 
  1. ax ∉ Y. In this case the following equivalence holds:
    (manger_merge_sets_new eqA addP Y (ax, bx)) =S= 
    (ax, bx) :: Y
    And we are home. 
  2. ax ∈ Y. In this case, we have 
      Y = Y₁ ++ [(ax, bx')] ++ Y₂ ∧
      ax ∉ (map fst Y₁) ∧ ax ∉ (map fst Y₂).
      
      Under these assumptions, the following 
      equivalence holds:
    2.1:
      (manger_merge_sets_new eqA addP Y (ax, bx)) =S=
      Y₁ ++ [(ax, bx + bx')] ++ Y₂

    2.2: And now the goal is almost trivial (Also, see
      the example at the top.)

    matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP 
        (Y₁ ++ [(ax, bx + bx')] ++ Y₂) U))
    =
    (matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP 
          ((ax, bx) :: Y₁ ++ [(ax, bx')] ++ Y₂) U)))
  *)

  
Admitted.

(* Some other trivial but annoying lemma *)
Lemma brel_set_uop_manger_phase_2 : 
  forall s1, 
  brel_set (brel_product eqA eqP) [] s1 = false ->
  brel_set (brel_product eqA eqP) [] 
    (uop_manger_phase_2 lteA s1) = false.
Proof.
  intros * Ha.

  case_eq (brel_set (brel_product eqA eqP) [] (uop_manger_phase_2 lteA s1));
  intros Hb; [rewrite <-Ha; eapply eq_sym|try reflexivity].
  eapply brel_set_nil in Hb.
  (* There is just one case uop_manger_phase_2 is empty 
    and that is when s1 = [] *)
Admitted.


Lemma uop_manger_phase_1_non_empty : 
  forall (X : finite_set (A * P)),
  brel_set (brel_product eqA eqP) [] X = false -> 
  brel_set (brel_product eqA eqP) [] 
    (uop_manger_phase_1 eqA addP X) = false.
Proof.
  intros * Ha.
Admitted.


Lemma brel_set_manger_product_phase_0_non_empty_backward : 
  forall (s t : finite_set (A * P)),
  brel_set (brel_product eqA eqP) [] s = false  -> 
  brel_set (brel_product eqA eqP) [] t = false ->
  brel_set (brel_product eqA eqP) []
    (manger_product_phase_0 eqA eqP mulA mulP s t) = false.
Proof.
  intros * Ha Hb.
Admitted.

(* End admit *)


(* Generalised accumulator *)
Lemma sum_fn_first_gen : 
  forall (X Y U : finite_set (A * P)) au,
  no_dup eqA (map fst Y) = true ->
  eqP
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (fold_left (manger_merge_sets_new eqA addP) X Y) U)))
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP (X ++ Y) U))) = true.
Proof.
  induction X as [|(ax, bx) X IHx].
  + intros * Ha; cbn;
    now rewrite list_filter_lib_filter_same, refP.
  +
    intros * Ha. simpl.
    (* instantiate Y with 
    (manger_merge_sets_new eqA addP Y (ax, bx))
    but I need to discharge no_dup for it *)
    eapply trnP; [eapply IHx |].
    ++
      (* true *)
      eapply no_dup_mmsn;
      try assumption.
      exact refP.
    ++
      (* seems provable *)
      (* 
        replace (manger_product_phase_0 eqA eqP mulA mulP
           ((ax, bx) :: X ++ Y) U) with 
        (manger_product_phase_0 eqA eqP mulA mulP
           (X ++ ((ax, bx) :: Y)) U)
        Now push the manger_product_phase_0 inside. 
      *)
      eapply symP, trnP;
      [eapply manger_product_phase_0_comm |].
      remember ((ax, bx) :: Y) as Ya.
      eapply trnP;
      [eapply manger_product_phase_0_dist | ].
      repeat rewrite filter_app.
      eapply trnP;
      [eapply sum_fn_distribute |]; 
      try assumption.
      eapply symP, trnP;
      [eapply manger_product_phase_0_dist | ].
      repeat rewrite filter_app.
      eapply trnP;
      [eapply sum_fn_distribute |]; 
      try assumption.
      eapply cong_addP;
      [eapply refP | subst].
      eapply manger_product_phase_0_manger_merge_interaction;
      exact Ha.
Qed.

  

    
Lemma sum_fn_second_gen : 
  forall (X Y U : finite_set (A * P)) au,
  no_dup eqA (map fst U) = true ->
  eqP
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X
        (fold_left (manger_merge_sets_new eqA addP) Y U))))
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X (Y ++ U)))) = true.
Proof.
  intros * Ha.
  (* Prove a lemma that:
  manger_product_phase_0 eqA eqP mulA mulP X Y =S= 
  manger_product_phase_0 eqA eqP mulA mulP Y X. 
  Then use it swap the arguments and use the lemma above. 
  *)
  remember ((fold_left (manger_merge_sets_new eqA addP) Y U)) as YU.
  eapply trnP with 
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP YU X))).
  +
    eapply sum_fn_congruence_general_set with 
    (eqA := eqA) (fA := fA) (lteA := lteA); try assumption;
    try (eapply addP_gen_idempotent);
    eapply filter_congruence_gen; try assumption.
    eapply bop_congruence_bProp_fst; try assumption.
    eapply brel_set_manger_product_phase_0_swap_v1.
  +
    eapply symP, trnP with 
    (matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP (Y ++ U) X))).
    ++
      eapply sum_fn_congruence_general_set with 
      (eqA := eqA) (fA := fA) (lteA := lteA); try assumption;
      try (eapply addP_gen_idempotent).
      repeat rewrite list_filter_lib_filter_same.
      eapply filter_congruence_gen; try assumption.
      eapply bop_congruence_bProp_fst; try assumption.
      eapply brel_set_manger_product_phase_0_swap_v1.
    ++
      subst. eapply symP.
      eapply sum_fn_first_gen; exact Ha.
Qed.




(*
This proof is similar to 
matrix_sum_fn_addition in manger_llex.v, 
but appears more difficult. 
*)
Lemma sum_fn_first : 
forall (X Y : finite_set (A * P)) au,
  eqP 
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP X) Y)))
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true.
Proof.
  intros *.
  unfold uop_manger_phase_1,
  manger_phase_1_auxiliary;
  rewrite manger_merge_set_funex.
  replace (X) with (X ++ []) at 2;
  [| eapply app_nil_r].
  eapply sum_fn_first_gen with (Y := []);
  reflexivity.
Qed.


Lemma sum_fn_second : 
  forall (X Y : finite_set (A * P)) au,
  eqP 
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X
        (uop_manger_phase_1 eqA addP Y)))) 
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true.
Proof.
  intros *.
  unfold uop_manger_phase_1,
  manger_phase_1_auxiliary;
  rewrite manger_merge_set_funex.
  replace (Y) with (Y ++ []) at 2;
  [| eapply app_nil_r];
  eapply sum_fn_second_gen;
  reflexivity.
Qed.





(* end of movement *)


Lemma sum_fn_forward_first : 
  forall (X Y : finite_set (A * P)) au av, 
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP X) Y))) = true ->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true.
Proof.
  intros * Ha.
  eapply trnP;
  [exact Ha | eapply sum_fn_first].
Qed.


Lemma sum_fn_backward_first : 
  forall (X Y : finite_set (A * P)) au av, 
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X Y ))) = true ->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP X) Y))) = true.
Proof.
  intros * Ha.
  eapply trnP;
  [exact Ha | 
  rewrite list_filter_lib_filter_same, 
  <-list_filter_lib_filter_same;
  eapply symP, sum_fn_first].
Qed.




Lemma sum_fn_forward_second : 
  forall (X Y : finite_set (A * P)) au av, 
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X
        (uop_manger_phase_1 eqA addP Y)))) = true ->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true.
Proof.
  intros * Ha.
  eapply trnP;
  [exact Ha | eapply sum_fn_second].
Qed.
  

Lemma sum_fn_backward_second : 
  forall (X Y : finite_set (A * P)) au av,
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true ->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X
        (uop_manger_phase_1 eqA addP Y)))) = true.
Proof.
  intros * Ha.
  eapply trnP;
  [exact Ha | 
  rewrite list_filter_lib_filter_same, 
  <-list_filter_lib_filter_same;
  eapply symP, sum_fn_second].
Qed.



(* *)
Lemma set_in_set_non_empty_left : 
  forall (X Y : finite_set (A * P)) au q, 
  set.in_set (brel_product eqA eqP)
    (manger_product_phase_0 eqA eqP mulA mulP X Y) (au, q) = true ->
  brel_set (brel_product eqA eqP) [] X = false.
Proof.
  intros * Ha.
  eapply in_set_bop_lift_elim in Ha;
  [| eapply refAP | eapply symAP];
  try assumption;
  destruct Ha as ((xa, xb) & (ya, yb) & (Ha, Hb) & Hc);
  destruct Y; destruct X; cbn in Ha, Hb; 
  try congruence;
  cbn; split; try reflexivity.
Qed.



Lemma set_in_set_non_empty_right : 
  forall (X Y : finite_set (A * P)) au q, 
  set.in_set (brel_product eqA eqP)
    (manger_product_phase_0 eqA eqP mulA mulP X Y) (au, q) = true ->
  brel_set (brel_product eqA eqP) [] Y = false.
Proof.
  intros * Ha.
  eapply in_set_bop_lift_elim in Ha;
  [| eapply refAP | eapply symAP];
  try assumption;
  destruct Ha as ((xa, xb) & (ya, yb) & (Ha, Hb) & Hc);
  destruct Y; destruct X; cbn in Ha, Hb; 
  try congruence;
  cbn; split; try reflexivity.
Qed.


Lemma brel_set_manger_product_phase_0_non_empty_forward : 
  forall (s t : finite_set (A * P)),
  brel_set (brel_product eqA eqP) []
    (manger_product_phase_0 eqA eqP mulA mulP s t) = false ->
  brel_set (brel_product eqA eqP) [] s = false ∧
  brel_set (brel_product eqA eqP) [] t = false.
Proof.
  intros * Ha.
  eapply brel_set_false_elim_prop in Ha.
  destruct Ha as [((a1, b1) & Ha & Hb) | 
  ((a1, b1) & Ha & Hb)].
  +
    cbn in Ha; congruence.
  +
    refine (conj _ _ );
    [eapply set_in_set_non_empty_left |
    eapply set_in_set_non_empty_right]; exact Ha.
  + eapply refAP; try assumption.
  + eapply symAP; try assumption.
Qed.



Lemma non_empty_list : 
  forall (X Y : finite_set (A * P)),
  (∀ a : A * P,
    set.in_set (manger_llex.eqAP A P eqA eqP) X a = true ->
    set.in_set (manger_llex.eqAP A P eqA eqP) Y a = true) ->
  brel_set (brel_product eqA eqP) [] X = false ->
  brel_set (brel_product eqA eqP) [] Y = false.
Proof.
  intros * Ha Hb.
  destruct X as [|(ax, bx) X];
  cbn in Hb |- *;
  [congruence |].
  specialize (Ha (ax, bx));
  cbn in Ha; rewrite refA, refP in Ha;
  cbn in Ha.
  specialize (Ha eq_refl).
  destruct Y;
  cbn in Ha |- *;
  [congruence | reflexivity].
Qed.



(* I can prove congruence assuming when both, 
mulA and mulP, are left or both are right *)
Lemma manger_product_phase_0_cong_left :
  bop_is_left A eqA mulA -> bop_is_left P eqP mulP -> 
  bop_congruence _ 
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros Hu Hv ? ? ? ? Ha Hb.
  eapply brel_set_elim_prop in Ha, Hb;
  [|eapply symAP | eapply trnAP | eapply symAP | eapply trnAP];
  try assumption; destruct Ha as (Hal & Har);
  destruct Hb as (Hbl & Hbr).
  eapply brel_set_intro_prop;
  [eapply refAP| split; intros (au, av) Hc];
  try assumption.
  +
    pose proof (set_in_set_non_empty_left _ _ _ _ Hc) as Hd.
    pose proof (set_in_set_non_empty_right _ _ _ _ Hc) as He.
    (* I know that s1 and s2 are non-empty *)
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Hc;
    [eapply symAP| eapply trnAP|]; try assumption.
    (* 
      Proof idea:
      from set.in_set (manger_llex.eqAP A P eqA eqP)
       (bop_list_product_left (bop_product mulA mulP) s1 s2) (
       au, av) = true 
      I know that (bop_list_product_left (bop_product mulA mulP) s1 s2) <> []
      from (bop_list_product_left (bop_product mulA mulP) s1 s2) <> []
      I know that s1 and s2 are non-empty
    *)

    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | eapply bop_product_is_left | | ]; 
    try assumption.
    ++  
      eapply bop_list_product_is_left_elim in Hc;
      [|eapply trnAP | eapply symAP | eapply bop_product_is_left]; 
      try assumption.
      eapply Hal; exact Hc.
    ++
      eapply non_empty_list;
      [exact Hbl | exact He].
      (* Provable *)
  + 
    pose proof (set_in_set_non_empty_left _ _ _ _ Hc) as Hd.
    pose proof (set_in_set_non_empty_right _ _ _ _ Hc) as He.

    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Hc;
    [eapply symAP| eapply trnAP|]; try assumption.
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | eapply bop_product_is_left | | ]; 
    try assumption.
    ++  
      eapply bop_list_product_is_left_elim in Hc;
      [|eapply trnAP | eapply symAP | eapply bop_product_is_left]; 
      try assumption.
      eapply Har; exact Hc.
    ++
      (* Provable *)
      eapply non_empty_list;
      [exact Hbr | exact He].
Qed.


Lemma manger_product_phase_0_cong_right :
  bop_is_right A eqA mulA -> bop_is_right P eqP mulP -> 
  bop_congruence _ 
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros Hu Hv ? ? ? ? Ha Hb.
  eapply brel_set_elim_prop in Ha, Hb;
  [|eapply symAP | eapply trnAP | eapply symAP | eapply trnAP];
  try assumption; destruct Ha as (Hal & Har);
  destruct Hb as (Hbl & Hbr).
  eapply brel_set_intro_prop;
  [eapply refAP| split; intros (au, av) Hc];
  try assumption.
  +
    pose proof (set_in_set_non_empty_left _ _ _ _ Hc) as Hd.
    pose proof (set_in_set_non_empty_right _ _ _ _ Hc) as He.
    (* I know that s1 and s2 are non-empty *)
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Hc;
    [eapply symAP| eapply trnAP|]; try assumption.
    (* 
      Proof idea:
      from set.in_set (manger_llex.eqAP A P eqA eqP)
       (bop_list_product_left (bop_product mulA mulP) s1 s2) (
       au, av) = true 
      I know that (bop_list_product_left (bop_product mulA mulP) s1 s2) <> []
      from (bop_list_product_left (bop_product mulA mulP) s1 s2) <> []
      I know that s1 and s2 are non-empty
    *)

    eapply bop_list_product_is_right_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_product_is_right | | ];
    try assumption.
    ++  
      eapply bop_list_product_is_right_elim in Hc;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right]; 
      try assumption.
      eapply Hbl; exact Hc.
    ++
      eapply non_empty_list;
      [exact Hal | exact Hd].
      (* Provable *)
  + 
    pose proof (set_in_set_non_empty_left _ _ _ _ Hc) as Hd.
    pose proof (set_in_set_non_empty_right _ _ _ _ Hc) as He.

    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Hc;
    [eapply symAP| eapply trnAP|]; try assumption.
    eapply bop_list_product_is_right_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_product_is_right | | ];
    try assumption.
    ++  
      eapply bop_list_product_is_right_elim in Hc;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right]; 
      try assumption.
      eapply Hbr; exact Hc.
    ++
      eapply non_empty_list;
      [exact Har | exact Hd].
Qed.

(* End of congruence *)




(* Assumes bop_is_left *)
Lemma bop_left_uop_inv_phase_1_left : 
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_1 eqA addP)
    (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_1 eqA addP).
Proof.
  intros Hu Hv ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +

    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [|eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption; try (eapply addP_gen_idempotent).
      eapply in_set_uop_manger_phase_1_elim with 
      (zeroP := zeroP) in Hal; try assumption;
      try (eapply addP_gen_idempotent);
      destruct Hal as ((qt & Hala) & Halb);
      exists qt;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      (* This is the challenge! Because it's 
        demanding s2 to be non-empty *)
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | 
      eapply bop_product_is_left | | ];
      try assumption.
    ++
      (* Think about it! *)
      eapply sum_fn_forward_first; 
      try assumption.
      
  +
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    ++
    
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [|eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption; eexists;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply bop_product_is_left | |];
      try assumption.
      *
        eapply in_set_uop_manger_phase_1_intro with 
        (zeroP := zeroP); try assumption;
        try (eapply addP_gen_idempotent);
        [exists q; exact Hal | eapply refP].
    ++
      (* Think about it! *)
      eapply sum_fn_backward_first;
      try assumption.
Qed.
    



Lemma bop_left_uop_inv_phase_1_right : 
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_1 eqA addP)
    (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_1 eqA addP).
Proof.
  intros Hu Hv ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +

    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    assert (Hc : brel_set (brel_product eqA eqP) [] s1 = false).
    destruct s1; cbn in Hal |- *; [congruence | reflexivity].
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hal;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption; try (eapply addP_gen_idempotent).
      exists q;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption.
      (* This is the challenge! Because it's 
        demanding s2 to be non-empty *)
      eapply bop_list_product_is_right_intro;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | 
      eapply bop_product_is_right | | ];
      try assumption.
    ++
      eapply sum_fn_forward_first;
      try assumption.
  +
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    assert (Hc : brel_set (brel_product eqA eqP) [] s1 = false).
    destruct s1; cbn in Hal |- *; [congruence | reflexivity].
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hal;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption; eexists;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      eapply bop_list_product_is_right_intro;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | eapply bop_product_is_right | |];
      try assumption.
      *
        exact Hal.
      *
        eapply uop_manger_phase_1_non_empty; 
        try assumption.
    ++
    eapply sum_fn_backward_first;
    try assumption.
Qed.



Lemma bop_right_uop_inv_phase_1_left : 
  bop_is_left A eqA mulA ->
  bop_is_left P eqP mulP -> 
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_1 eqA addP)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_1 eqA addP).
Proof.
  intros Hu Hv ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  + 
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    destruct s2; cbn in Hal |- *.
    eapply set_in_set_non_empty_right in Hal; cbn in Hal;
    congruence. reflexivity.
    assert (Hc :  brel_set (brel_product eqA eqP) [] s1 = false).
    destruct s1; cbn in Hal |- *;
    [congruence | reflexivity].
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [ | eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption.
      exists q.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption.
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | 
      eapply bop_product_is_left | | ];
      try assumption.
    ++
      (* Think about it! *)
      eapply sum_fn_forward_second;
      try assumption.
  +
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    destruct s2; cbn in Hal |- *.
    eapply set_in_set_non_empty_right in Hal; cbn in Hal;
    congruence. reflexivity.
    assert (Hc :  brel_set (brel_product eqA eqP) [] s1 = false).
    destruct s1; cbn in Hal |- *;
    [congruence | reflexivity].
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [ | eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption.
      exists q.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption.
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | 
      eapply bop_product_is_left | | ];
      try assumption.
      *
      eapply uop_manger_phase_1_non_empty; 
      try assumption.
    ++
      eapply sum_fn_backward_second;
      try assumption.
Qed.


Lemma bop_right_uop_inv_phase_1_right : 
  bop_is_right A eqA mulA ->
  bop_is_right P eqP mulP -> 
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_1 eqA addP)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_1 eqA addP).
Proof.
  intros Hu Hv ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  + 
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    destruct s2; cbn in Hal |- *.
    eapply set_in_set_non_empty_right in Hal; cbn in Hal;
    congruence. reflexivity.
    assert (Hc :  brel_set (brel_product eqA eqP) [] s1 = false).
    destruct s1; cbn in Hal |- *;
    [congruence | reflexivity].
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim,
      in_set_uop_manger_phase_1_elim with 
      (zeroP := zeroP) in Hal; try assumption;
      [| eapply addP_gen_idempotent | eapply refAP | 
        eapply trnAP | eapply symAP | eapply bop_product_is_right];
      try assumption; destruct Hal as ((qt & Hala) & Halb).
      (* this qt is going to be the witness *)
      exists qt.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ]; try assumption.
      eapply bop_list_product_is_right_intro;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | eapply bop_product_is_right | 
      | exact Hc]; try assumption.
    ++
      (* May require some thinking*)
      eapply sum_fn_forward_second;
      try assumption.
  +
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s1 = false).
    destruct s1; cbn in Hal |- *; congruence.
    ++

      eexists;
      eapply union.in_set_uop_duplicate_elim_intro;
      eapply union.in_set_uop_duplicate_elim_elim in Hal;
      [eapply symAP| eapply trnAP|]; try assumption;
      try (eapply addP_gen_idempotent);
      eapply bop_list_product_is_right_intro;
      [eapply refAP | eapply trnAP | eapply symAP |
        eapply bop_cong | eapply bop_product_is_right | | exact Hb];
      try assumption; try (eapply addP_gen_idempotent);
      eapply bop_list_product_is_right_elim in Hal;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right]; try assumption;
      try (eapply addP_gen_idempotent);
      eapply in_set_uop_manger_phase_1_intro with 
      (zeroP := zeroP); try assumption;
      try (eapply addP_gen_idempotent);
      [eexists; exact Hal | eapply refP].
    ++
      (* This about it *)
      eapply sum_fn_backward_second;
      try assumption.
Qed.





Lemma bop_left_uop_inv_phase_2_left : 
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_2 lteA)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_2 lteA).
Proof.
  intros Hu Hv ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
    destruct Ha as (Hal & Har);
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [|eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption;
      eapply in_set_uop_manger_phase_2_elim in Hal; try assumption;
      destruct Hal as (Hala & Halb);
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      (* This is the challenge! Because it's 
        demanding s2 to be non-empty *)
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply bop_product_is_left | | ];
      try assumption.
    ++
      intros ? ? Hb.
      eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
      destruct Ha as (Hal & Har).
      eapply union.in_set_uop_duplicate_elim_elim, 
      bop_list_product_is_left_elim,
      in_set_uop_manger_phase_2_elim in Hal;
      try assumption;
      [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption.
      destruct Hal as (Hala & Halb).
      eapply Halb.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hb;
      [exact Hb | eapply trnAP | eapply symAP | 
      eapply bop_product_is_left];
      try assumption.
  +
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption.
    destruct Ha as (Hal & Har).
    assert (Hq : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    ++
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      eapply  bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply bop_product_is_left | |
        exact Hq]; try assumption;
      eapply union.in_set_uop_duplicate_elim_elim, 
      bop_list_product_is_left_elim in Hal;
      [|eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption;
      eapply in_set_uop_manger_phase_2_intro;
      try assumption;
      intros * Hc; eapply Har;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      eapply  bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply bop_product_is_left | |
      exact Hq]; try assumption;
      exact Hc.
    ++
      intros ? ? Hb.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption; eapply Har;
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hb;
      [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply in_set_uop_manger_phase_2_elim in Hb;
      try assumption;
      destruct Hb as (Hbl & Hbr);
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply 
      bop_product_is_left | exact Hbl | ];
      try assumption.
Qed.





(* is this provable using bop_right?? *)
Lemma bop_left_uop_inv_phase_2_right : 
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_2 lteA)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_2 lteA).
Proof.
  intros Hu Hv ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
    destruct Ha as (Hal & Har);
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    assert (Hc : brel_set (brel_product eqA eqP) [] s1 = false).
    destruct s1; cbn in Hal |- *;
    [congruence | reflexivity].
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hal;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      (* This is the challenge! Because it's 
        demanding s2 to be non-empty *)
      eapply bop_list_product_is_right_intro;
      [eapply refAP | eapply trnAP | eapply symAP | 
        eapply bop_cong | eapply bop_product_is_right | exact Hal | 
        exact Hc];
      try assumption.
    ++
      intros ? ? Hb.
      eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
      destruct Ha as (Hal & Har).
      assert (Hc : brel_set (brel_product eqA eqP) [] s2 = false).
      eapply set_in_set_non_empty_right; exact Hal.
      assert (Hd : brel_set (brel_product eqA eqP) [] s1 = false).
      destruct s1; cbn in Hal |- *;
      [congruence | reflexivity].
      assert (He : brel_set (brel_product eqA eqP) [] 
        (uop_manger_phase_2 lteA s1) = false).
      eapply set_in_set_non_empty_left in Hal; 
      exact Hal.
      (* tricky *)
      eapply union.in_set_uop_duplicate_elim_elim, 
      bop_list_product_is_right_elim in Hal;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hb;
      [| eapply refAP  | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
      eapply Har;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply bop_list_product_is_right_intro;
      [eapply  refAP | eapply  trnAP | eapply  symAP|
      eapply bop_cong | eapply bop_product_is_right | exact Hb | ];
      try assumption.
  +

    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption.
    destruct Ha as (Hal & Har).
    assert (Hq : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    assert (Hp :  brel_set (brel_product eqA eqP) [] s1 = false).
    eapply set_in_set_non_empty_left in Hal; exact Hal.
    (* challenge with this proof is that when I am going 
      right, it demands me (uop_manger_phase_2 lteA s1) to 
      be non-empty. Since s1 is non-empty it's minimisation 
      would also be non-empty  *)
    assert (Ht : brel_set (brel_product eqA eqP) [] 
      (uop_manger_phase_2 lteA s1) = false).
    eapply brel_set_uop_manger_phase_2; exact Hp.
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    ++
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      eapply  bop_list_product_is_right_intro;
      [eapply refAP | eapply trnAP | eapply symAP | 
        eapply bop_cong | eapply bop_product_is_right | 
      | ]; try assumption.
      eapply union.in_set_uop_duplicate_elim_elim, 
      bop_list_product_is_right_elim in Hal;
      [exact Hal |eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
    ++
      intros * Hb.
      (* tricky *)
      eapply union.in_set_uop_duplicate_elim_elim, 
      bop_list_product_is_right_elim in Hal;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hb;
      [| eapply refAP  | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
      eapply Har;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply bop_list_product_is_right_intro;
      [eapply  refAP | eapply  trnAP | eapply  symAP|
      eapply bop_cong | eapply bop_product_is_right | exact Hb | ];
      try assumption.
Qed.



Lemma bop_right_uop_inv_phase_2_left : 
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_2 lteA)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_2 lteA).
Proof.
  intros Hu Hv ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
    destruct Ha as (Hal & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] 
      (uop_manger_phase_2 lteA s2) = false).
    eapply set_in_set_non_empty_right; exact Hal.
    assert (Hc : brel_set (brel_product eqA eqP) [] s2 = false).
    destruct s2; cbn in Hb; try congruence;
    cbn; try reflexivity.
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption.
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply 
      bop_product_is_left | exact Hal | exact Hc];
      try assumption.
    ++
      intros * Hd.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption; eapply Har;
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hd;
      [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption.
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply 
      bop_product_is_left | exact Hd | ];
      try assumption.
  +
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption.
    destruct Ha as (Hal & Har).
    assert (Hq : brel_set (brel_product eqA eqP) [] s1 = false).
    eapply set_in_set_non_empty_left; exact Hal.
    assert (Hw : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    assert (Ht : brel_set (brel_product eqA eqP) [] 
      (uop_manger_phase_2 lteA s2) = false).
    eapply brel_set_uop_manger_phase_2; exact Hw.
    (* go left *)
    eapply in_set_uop_manger_phase_2_intro;
    try assumption.
    ++
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply bop_list_product_is_left_intro;
      [eapply  trnAP | eapply  symAP|
       eapply bop_product_is_left | | exact Ht];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [exact Hal | eapply  trnAP | eapply  symAP|
      eapply bop_product_is_left];
      try assumption.
    ++
      intros * Hb.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption. eapply Har.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hb;
      [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply 
      bop_product_is_left | exact Hb | ];
      try assumption.
Qed.



Lemma bop_right_uop_inv_phase_2_right : 
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_2 lteA)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_2 lteA).
Proof.
  intros Hu Hv ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
    destruct Ha as (Hal & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] 
      (uop_manger_phase_2 lteA s2) = false).
    eapply set_in_set_non_empty_right; exact Hal.
    assert (Hc : brel_set (brel_product eqA eqP) [] s2 = false).
    destruct s2; cbn in Hb; try congruence;
    cbn; try reflexivity.
    assert (Hw : brel_set (brel_product eqA eqP) [] s1 = false).
    eapply set_in_set_non_empty_left; exact Hal.
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    ++  
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hal;
      [| eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption.
      eapply bop_list_product_is_right_intro;
      [eapply refAP | eapply trnAP | eapply symAP | 
        eapply bop_cong | eapply 
      bop_product_is_right | eapply in_set_uop_manger_phase_2_elim in Hal 
      | exact Hw]; try assumption.
      exact (proj1 Hal).
    ++
      intros * Hd.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hal;
      [| eapply refAP | eapply trnAP | eapply symAP | 
        eapply bop_product_is_right];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hd;
      [| eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
      eapply in_set_uop_manger_phase_2_elim in Hal;
      try assumption;
      destruct Hal as (Hala & Halb).
      eapply Halb; exact Hd.   
  +
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption.
    assert (Hq : brel_set (brel_product eqA eqP) [] s1 = false).
    eapply set_in_set_non_empty_left; exact (proj1 Ha).
    assert (Hw : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact (proj1 Ha).
    assert (Ht : brel_set (brel_product eqA eqP) [] 
      (uop_manger_phase_2 lteA s2) = false).
    eapply brel_set_uop_manger_phase_2; exact Hw.
    destruct Ha as (Hal & Har).
    eapply in_set_uop_manger_phase_2_intro;
    try assumption.
    ++
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply bop_list_product_is_right_intro;
      [eapply refAP | eapply  trnAP | eapply  symAP|
      eapply bop_cong | eapply bop_product_is_right | | exact Hq];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hal;
      [ | eapply refAP | eapply  trnAP | eapply  symAP|
      eapply bop_product_is_right];
      try assumption.
      eapply in_set_uop_manger_phase_2_intro; try assumption;
      intros * Hb; eapply Har.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption.
      eapply bop_list_product_is_right_intro;
      [eapply  refAP | eapply  trnAP | eapply  symAP|
      eapply bop_cong | eapply bop_product_is_right | exact Hb | ];
      try assumption.
    ++
      intros * Hb.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hal;
      [| eapply refAP | eapply trnAP | eapply symAP |
       eapply bop_product_is_right];
      try assumption. 
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hb;
      [| eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_product_is_right];
      try assumption.
      eapply in_set_uop_manger_phase_2_elim in Hb;
      try assumption;
      destruct Hb as (Haba & Hbb).
      eapply Har.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ]; try assumption.
      eapply bop_list_product_is_right_intro;
      [eapply  refAP | eapply  trnAP | eapply  symAP|
      eapply bop_cong | eapply bop_product_is_right | exact Haba | ];
      try assumption.
Qed.
      



Lemma bop_manger_product_congruence_left :
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_congruence _ (@eq_manger A P eqA lteA eqP addP) 
    (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  eapply uop_compose_bop_congruence.
  + eapply symSAP.
  + eapply trnSAP; 
    try assumption.
  + eapply manger_product_phase_0_cong_left;
    try assumption.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1_left; 
    try assumption.
  + eapply bop_right_uop_inv_phase_1_left;
    try assumption.
  + eapply P2_cong; try assumption.
  + eapply bop_left_uop_inv_phase_2_left; 
    try assumption.
  + eapply bop_right_uop_inv_phase_2_left;
    try assumption.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption;
    try (eapply addP_gen_idempotent).
Qed.

Lemma bop_manger_product_congruence_right :
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_congruence _ (@eq_manger A P eqA lteA eqP addP) 
    (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  eapply uop_compose_bop_congruence.
  + eapply symSAP.
  + eapply trnSAP; 
    try assumption.
  + eapply manger_product_phase_0_cong_right;
    try assumption.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1_right; 
    try assumption.
  + eapply bop_right_uop_inv_phase_1_right;
    try assumption.
  + eapply P2_cong; try assumption.
  + eapply bop_left_uop_inv_phase_2_right; 
    try assumption.
  + eapply bop_right_uop_inv_phase_2_right;
    try assumption.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption;
    try (eapply addP_gen_idempotent).
Qed.



Lemma manger_product_phase_0_associative_left :
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_associative (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros Hu Hv ? ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; 
  try assumption.
  +
    (* do a bunch of preprocessing here *)
    (* prove that s <> [], t <> [], u <> []
      and bunch of other combinations *)
    assert (Hb : brel_set (brel_product eqA eqP) [] 
      (manger_product_phase_0 eqA eqP mulA mulP s t) = false).
    eapply set_in_set_non_empty_left; exact Ha.
    assert (Hc : brel_set (brel_product eqA eqP) [] u = false).
    eapply set_in_set_non_empty_right; exact Ha.
    eapply brel_set_manger_product_phase_0_non_empty_forward in Hb.
    destruct Hb as (Hbl & Hbr).
    assert (Hb :  brel_set (brel_product eqA eqP) []
    (manger_product_phase_0 eqA eqP mulA mulP t u) = false).
    eapply brel_set_manger_product_phase_0_non_empty_backward;
    try assumption.

    (* actual proof *)
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    (* go left  *)
    eapply bop_list_product_is_left_elim in Ha;
    [ |  eapply trnAP | eapply symAP | 
    eapply bop_product_is_left]; try assumption.
    eapply union.in_set_uop_duplicate_elim_elim, 
    bop_list_product_is_left_elim in Ha;
    [| eapply trnAP|eapply symAP| eapply 
    bop_product_is_left ]; try assumption.
    (* go left  *)
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | eapply 
    bop_product_is_left | exact Ha | ];
    try assumption.
  +
    assert (Hb : brel_set (brel_product eqA eqP) [] u = false).
    eapply set_in_set_non_empty_right in Ha.
    eapply  brel_set_manger_product_phase_0_non_empty_forward in Ha;
    exact (proj2 Ha).
    assert (Hc : brel_set (brel_product eqA eqP) [] t = false).
    eapply set_in_set_non_empty_right in Ha.
    eapply  brel_set_manger_product_phase_0_non_empty_forward in Ha;
    exact (proj1 Ha).
    (* actual proof *)
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    (* go left  *)
    eapply bop_list_product_is_left_elim in Ha;
    [ |  eapply trnAP | eapply symAP | 
    eapply bop_product_is_left]; try assumption.
    (* go left  *)
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | eapply 
    bop_product_is_left |  | exact Hb];
    try assumption.
    eapply union.in_set_uop_duplicate_elim_intro,
    bop_list_product_is_left_intro;
    [eapply symAP | eapply trnAP | eapply trnAP | 
    eapply symAP | eapply bop_product_is_left |
    | exact Hc]; try assumption.
Qed.

    

Lemma manger_product_phase_0_associative_right :
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_associative (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros Hu Hv ? ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; 
  try assumption.
  +
    (* I need some preprocessing here *)
    assert (Hb : brel_set (brel_product eqA eqP) [] s = false).
    eapply set_in_set_non_empty_left in Ha;
    eapply  brel_set_manger_product_phase_0_non_empty_forward in Ha;
    exact (proj1 Ha).
    assert (Hc : brel_set (brel_product eqA eqP) [] t = false).
    eapply set_in_set_non_empty_left in Ha.
    eapply  brel_set_manger_product_phase_0_non_empty_forward in Ha;
    exact (proj2 Ha).
    (* actual proof *)
    (* go right *)
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    (* go left  *)
    eapply bop_list_product_is_right_elim in Ha;
    [ |  eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_product_is_right]; try assumption.
    eapply bop_list_product_is_right_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply 
    bop_product_is_right | | exact Hb];
    try assumption.
    eapply union.in_set_uop_duplicate_elim_intro,
    bop_list_product_is_right_intro;
    [eapply symAP | eapply trnAP | 
    eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_product_is_right | 
    exact Ha | exact Hc]; try assumption.
  +
    (* some preprocessing*)
    assert (Hb : brel_set (brel_product eqA eqP) [] s = false).
    eapply set_in_set_non_empty_left in Ha; exact Ha.
    assert (Hc : brel_set (brel_product eqA eqP) [] t = false).
    eapply set_in_set_non_empty_right in Ha.
    eapply brel_set_manger_product_phase_0_non_empty_forward in Ha;
    exact (proj1 Ha).
    assert (Hd : brel_set (brel_product eqA eqP) []
    (manger_product_phase_0 eqA eqP mulA mulP s t) = false).
    eapply brel_set_manger_product_phase_0_non_empty_backward;
    try assumption.
    (* actual proof *)
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    eapply bop_list_product_is_right_elim in Ha;
    [ |  eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_product_is_right]; try assumption.
    eapply union.in_set_uop_duplicate_elim_elim, 
    bop_list_product_is_right_elim in Ha;
    [|eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_product_is_right]; try assumption.
    eapply bop_list_product_is_right_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_product_is_right | 
    exact Ha | ]; try assumption.
  Qed.



Lemma bop_manger_product_associative_left :
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_associative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  apply uop_compose_bop_associative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong_left; 
    try assumption.
  + eapply  manger_product_phase_0_associative_left; 
    try assumption.
  + eapply P1_cong with (fA := fA) (zeroP := zeroP) (lteA := lteA); 
    try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1_left; 
    try assumption.
  + eapply bop_right_uop_inv_phase_1_left; 
    try assumption.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2_left; 
    try assumption.
  + eapply bop_right_uop_inv_phase_2_left; 
    try assumption.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
Qed.


Lemma bop_manger_product_associative_right :
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_associative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  apply uop_compose_bop_associative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong_right; 
    try assumption.
  + eapply  manger_product_phase_0_associative_right; 
    try assumption.
  + eapply P1_cong with (fA := fA) (zeroP := zeroP) (lteA := lteA); 
    try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1_right; 
    try assumption.
  + eapply bop_right_uop_inv_phase_1_right; 
    try assumption.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2_right; 
    try assumption.
  + eapply bop_right_uop_inv_phase_2_right; 
    try assumption.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
Qed.


(* This require mulA and mulP to be commutative  *)
Lemma manger_product_phase_0_commutative: 
  bop_commutative (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    eapply in_set_list_product_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption.
    destruct Ha as ((xa, xb) & (ya, yb) & (Hb & Hc) & Hd). 
    unfold manger_llex.eqAP in Hd.
    (* What an awesome proof! This requires 
      mulA and mulP to commutative.
    *)
    assert (He : brel_product eqA eqP (au, av)
      (bop_product mulA mulP (ya, yb) (xa, xb)) = true).
    eapply brel_product_intro;
    eapply brel_product_elim in Hd;
    destruct Hd as (Hdl & Hdr);
   [exact (trnA _ _ _ Hdl (mulA_comm xa ya)) |
    exact (trnP _ _ _ Hdr (mulP_comm xb yb))].
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (ya, yb) (xa, xb));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric | ];
    try assumption. 
    eapply in_set_list_product_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | exact Hc | exact Hb];
    try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    eapply in_set_list_product_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption.
    destruct Ha as ((xa, xb) & (ya, yb) & (Hb & Hc) & Hd). 
    unfold manger_llex.eqAP in Hd.
    assert (He : brel_product eqA eqP (au, av)
      (bop_product mulA mulP (ya, yb) (xa, xb)) = true).
    eapply brel_product_intro;
    eapply brel_product_elim in Hd;
    destruct Hd as (Hdl & Hdr);
     [exact (trnA _ _ _ Hdl (mulA_comm xa ya)) |
      exact (trnP _ _ _ Hdr (mulP_comm xb yb))].
    (*Now replace the pair (au, av) by He. 
      apply in_set_list_product_intro
    *)
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (ya, yb) (xa, xb));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric | ];
    try assumption. 
    eapply in_set_list_product_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | exact Hc | exact Hb];
    try assumption.
Qed.
  

Lemma bop_manger_product_commutative_left :
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_commutative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  eapply uop_compose_bop_commutative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong_left;
    try assumption.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption; 
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1_left;
    try assumption.
  + eapply bop_right_uop_inv_phase_1_left;
    try assumption.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2_left;
    try assumption.
  + eapply bop_right_uop_inv_phase_2_left;
    try assumption.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
  + eapply manger_product_phase_0_commutative.
Qed.

Lemma bop_manger_product_commutative_right :
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_commutative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  eapply uop_compose_bop_commutative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong_right;
    try assumption.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption; 
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1_right;
    try assumption.
  + eapply bop_right_uop_inv_phase_1_right;
    try assumption.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2_right;
    try assumption.
  + eapply bop_right_uop_inv_phase_2_right;
    try assumption.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
  + eapply manger_product_phase_0_commutative.
Qed.


Lemma manger_product_phase_0_idem_left : 
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_idempotent (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros Hu Hv ?;
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha];
  try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_elim,
    bop_list_product_is_left_elim in Ha;
    [| eapply trnAP | eapply symAP | eapply bop_product_is_left];
    try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    [eapply symAP | eapply trnAP | ];
    try assumption;
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | apply symAP | eapply bop_product_is_left | 
      exact Ha | ];
    try assumption;
    destruct s; cbn in Ha;
    try congruence; 
    cbn; reflexivity.
Qed.



Lemma manger_product_phase_0_idem_right : 
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_idempotent (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros Hu Hv ?;
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha];
  try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_elim,
    bop_list_product_is_right_elim in Ha;
    [exact Ha | eapply refAP | eapply trnAP | eapply symAP 
    | eapply bop_product_is_right];
    try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    [eapply symAP | eapply trnAP | ];
    try assumption;
    eapply bop_list_product_is_right_intro;
    [eapply refAP | eapply trnAP | apply symAP | 
    eapply bop_cong | eapply bop_product_is_right | 
    exact Ha | ];
    try assumption;
    destruct s; cbn in Ha;
    try congruence; 
    cbn; reflexivity.
Qed.






Lemma bop_manger_product_idempotent_left :
  bop_is_left A eqA mulA -> 
  bop_is_left P eqP mulP ->
  bop_idempotent _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  eapply uop_compose_bop_idempotent.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong_left;
    try assumption.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1_left;
    try assumption.
  + eapply bop_right_uop_inv_phase_1_left;
    try assumption.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2_left;
    try assumption.
  + eapply bop_right_uop_inv_phase_2_left;
    try assumption.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
  + eapply  manger_product_phase_0_idem_left;
    try assumption.
Qed.
  
Lemma bop_manger_product_idempotent_right :
  bop_is_right A eqA mulA -> 
  bop_is_right P eqP mulP ->
  bop_idempotent _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  eapply uop_compose_bop_idempotent.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong_right;
    try assumption.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1_right;
    try assumption.
  + eapply bop_right_uop_inv_phase_1_right;
    try assumption.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2_right;
    try assumption.
  + eapply bop_right_uop_inv_phase_2_right;
    try assumption.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
  + eapply  manger_product_phase_0_idem_right;
    try assumption.
Qed.

(* Everything good upto this point *) 


(* With the assumption that we have, this is not 
provable. *)
Lemma bop_manger_product_not_selective :
  bop_not_selective _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  (* intros Hu Hv. *)
  destruct ntot as ((a₁, a₂) & Ha);
  exists ([(a₁, wP)], [(a₂, wP)]); compute;
  case_eq (eqA (mulA a₁ a₂) a₁); 
  case_eq (eqP (mulP wP wP) wP);
  case_eq (eqA a₁ (mulA a₁ a₂));
  case_eq (eqP wP (mulP wP wP));
  case_eq (eqA (mulA a₁ a₂) a₂);
  case_eq (eqP (mulP wP wP) wP);
  case_eq (eqA a₂ (mulA a₁ a₂));
  case_eq (eqP wP (mulP wP wP));
  intros Hb Hc Hd He Hf Hg Hi Hj;
  try eauto.
  +
    eapply symA in Hc.
    pose proof (trnA _ _ _ (symA _ _ Hj) Hc) as Hk.
    destruct Ha as (Hal & Har).
    assert (Hl := conLte _ _ _ _ (refA a₁) Hk).
    rewrite <-Hl in Hal.
    rewrite (refLte a₁) in Hal; congruence.
  + rewrite (symA _ _ Hc) in He; 
    congruence.
  +
    destruct Ha as (Hal & Har).
    (* case where a₁ and a₂ are incomprable  *)
    (* What can I infer from Hal and Har *)
    (* We need some extra condition to prove this? *)
    admit.
    
  +
    rewrite (symA _ _ Hj) in Hg; 
    congruence.
  +
    rewrite (symA _ _ Hg) in Hj; 
    congruence.
  +
    destruct Ha as (Hal & Har).
    (* case where a₁ and a₂ are incomprable  *)
    admit.
Admitted.  

End Theory.  



