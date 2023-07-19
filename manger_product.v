Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.bs.properties. 
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

(* 
 Print bop_lift. 
 Print bop_list_product_left.
 Print ltran_list_product.
 Print uop_manger.
 Print uop_manger_phase_1.
 Print manger_phase_1_auxiliary.
*)

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
Compute (manger_add (manger_mul s5 s1) (manger_mul s5 s3)). 
(* (1, 7, 10) :: (2, 4, 9) :: nil *) 
Compute (manger_mul s5 (manger_add s1 s3)).                 
(* (2, 4, 9) :: (1, 7, 10) :: nil *) 

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
  (cong_mulA : bop_congruence A eqA mulA)
  (cong_mulP : bop_congruence P eqP mulP)
  (mulP_addP_right_distributive : 
    (bop_right_distributive P eqP addP mulP)).

Local Notation "[EQP0]" :=  (brel_set (brel_product eqA eqP)) (only parsing).
Local Notation "[EQP1]" :=  (equal_manger_phase_1 eqA eqP addP) (only parsing). 
Local Notation "[MP1]" :=  (uop_manger_phase_1 eqA addP) (only parsing).
Local Notation "[MPP0]" :=  (manger_product_phase_0 eqA eqP mulA mulP) (only parsing).
Local Notation "[MP]" := (bop_manger_product eqA lteA eqP addP mulA mulP) (only parsing). 
Local Notation "[MR]" := (@uop_manger_phase_2 A P lteA) (only parsing).
Local Notation "[EQ]" := (equal_manger eqA lteA eqP addP) (only parsing).


    

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

Local Notation "x =S= y" := (manger_llex.eqSAP A P eqA eqP x y  = true) 
  (at level 70, only parsing).
Local Notation "a == b"   := (brel_product eqA eqP a b = true) 
  (at level 70).


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
Lemma brel_set_manger_product_phase_0_swap_v1 
  (mulA_comm : bop_commutative A eqA mulA)
  (mulP_comm : bop_commutative P eqP mulP) : 
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


Lemma manger_product_phase_0_cong : 
  bop_congruence _ 
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros ? ? ? ? Ha Hb.
  eapply brel_set_elim_prop in Ha, Hb;
  [| eapply symAP| eapply trnAP| eapply symAP|
  eapply trnAP]; try assumption;
  destruct Ha as (Hal & Har);
  destruct Hb as (Hbl & Hbr).
  eapply brel_set_intro_prop;
  [eapply refAP| split; intros (au, av) Hc];
  try assumption.
  +
    eapply in_set_bop_lift_elim in Hc;
    [| eapply refAP | eapply symAP];
    try assumption;
    destruct Hc as ((xa, xb) & (ya, yb) & (Ha, Hb) & Hc).
    eapply in_set_bop_lift_intro_v2;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply Hal; exact Ha |  eapply Hbl; exact Hb | 
    exact Hc]; try assumption.
  +
    eapply in_set_bop_lift_elim in Hc;
    [| eapply refAP | eapply symAP];
    try assumption;
    destruct Hc as ((xa, xb) & (ya, yb) & (Ha, Hb) & Hc).
    eapply in_set_bop_lift_intro_v2;
    [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong | 
    eapply Har; exact Ha | eapply Hbr; exact Hb | exact Hc ];
    try assumption.
Qed.


Lemma filter_not_in_set_no_dup : 
  forall (Y : finite_set (A * P)) (ah : A),
  set.in_set eqA (map fst Y) ah = false ->
  filter (λ '(s2, _), eqA ah s2) Y = [] ∧
  filter (λ '(s2, _), negb (eqA ah s2)) Y = Y.
Proof.
  induction Y as [|(ax, bx) Y IHy].
  +
    cbn; intros ? Ha.
    auto.
  +
    cbn; intros ? Ha.
    case_eq (eqA ah ax);
    cbn; intros Hb.
    rewrite Hb in Ha.
    cbn in Ha; congruence. 
    rewrite Hb in Ha; 
    cbn in Ha.
    destruct (IHy _ Ha) as (IHl & IHr).
    split; auto.
    f_equal. auto.
Qed.




Lemma uop_dup_elim_membership_cong : 
  forall (X : finite_set (A * P)),
  set.uop_duplicate_elim (brel_product eqA eqP) X =S= X.
Proof.
  intros *. 
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (xa, xb) Ha];
  try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_elim; try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    [eapply symAP | eapply trnAP | exact Ha];
    try assumption.
Qed.


Lemma ltrans_list_app : 
  forall(X Y : list (A * P)) (ah : A) (bh : P),
  ltran_list_product (bop_product mulA mulP) (ah, bh) (X ++ Y) = 
  ltran_list_product (bop_product mulA mulP) (ah, bh) X ++ 
  ltran_list_product (bop_product mulA mulP) (ah, bh) Y.
Proof.
  induction X as [|(ax, bx) X IHx].
  +
    simpl; intros; reflexivity.
  +
    simpl; intros *.
    rewrite IHx; f_equal.
Qed.

Lemma manger_merge_set_no_dup : 
  forall (X Y : finite_set (A * P)), 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst
    (fold_left (manger_merge_sets_new eqA addP) X Y)) = true.
Proof.
  induction X as [|(ax, bx) X IHx].
  +
    simpl; intros * Ha.
    exact Ha.
  +
    simpl; intros * Ha.
    eapply IHx.
    eapply no_dup_mmsn with (eqP := eqP);
    try assumption.
Qed.

(*  begin Admit *)

(* it is true! *)
Lemma mmsn_diff_swap_gen : 
  forall V au av ax bx, 
  ((manger_merge_sets_new eqA addP) 
    ((manger_merge_sets_new eqA addP) V (au, av)) (ax, bx)) =S= 
  ((manger_merge_sets_new eqA addP) 
    ((manger_merge_sets_new eqA addP) V (ax, bx)) (au, av)).
Proof.
  intros ? ? ? ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ma, mb) Ha];
  try assumption.
  +
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP];
    try assumption.
    eapply set.in_set_concat_intro.
    destruct Ha as [Ha | Ha].
    ++
      left; simpl in Ha |- *.
      cbn in Ha |- *.
      repeat rewrite <-list_filter_lib_filter_same in Ha |- *.
      repeat rewrite filter_app in Ha |- *.
      eapply set.in_set_concat_elim in Ha;
      [| eapply symAP]; try assumption.
      eapply set.in_set_concat_intro.
      destruct Ha as [Ha | Ha];
      [left | right].
      +++
        rewrite filter_filter_curry  in Ha |- *.
        rewrite <-Ha.
        f_equal. f_equal.
        eapply FunctionalExtensionality.functional_extensionality;
        intros (am, bm).
        case_eq (eqA au am);
        case_eq (eqA ax am);
        intros Hb Hc; cbn;
        try reflexivity.
      +++
         
Admitted.
(* end *)



Lemma fold_left_cong_aux_aux_1 :
  forall (X Y : finite_set (A * P)) au bu ax bx,
  no_dup eqA (map fst Y) = true ->
  eqA ax au = true ->
  eqP bx bu = true ->
  (fold_left (manger_merge_sets_new eqA addP) X
    (manger_merge_sets_new eqA addP
      (manger_merge_sets_new eqA addP Y (au, bu)) (ax, bx))) =S=
  (fold_left (manger_merge_sets_new eqA addP) X
     (manger_merge_sets_new eqA addP Y (au, bu))).
Proof.
Admitted.


(* use mmsn_diff_swap *)
Lemma fold_left_cong_aux_aux_2 :
  forall (X Y : finite_set (A * P)) au bu ax bx,
  no_dup eqA (map fst Y) = true ->
  eqA ax au = false ->
  (fold_left (manger_merge_sets_new eqA addP) X
    (manger_merge_sets_new eqA addP
      (manger_merge_sets_new eqA addP Y (ax, bx)) (au, bu))) =S= 
  (fold_left (manger_merge_sets_new eqA addP) X
    (manger_merge_sets_new eqA addP
      (manger_merge_sets_new eqA addP Y (au, bu)) (ax, bx))).
Proof.
Admitted.



Lemma fold_left_cong_aux_aux_3 :
  forall (X Y : finite_set (A * P)) au bu ax bx,
  no_dup eqA (map fst Y) = true -> 
  eqA ax au = true ->
  (* eqP bx bu = false *) (* I don't need but keep it *)
  (fold_left (manger_merge_sets_new eqA addP) X
    (manger_merge_sets_new eqA addP
      (manger_merge_sets_new eqA addP Y (au, bu)) (ax, bx))) =S= 
  (fold_left (manger_merge_sets_new eqA addP) X
    (manger_merge_sets_new eqA addP Y (au, addP bu bx))).
Proof.
Admitted.





Lemma fold_left_cong_aux_1 : 
  forall (X Y : finite_set (A * P)) au bu, 
  no_dup eqA (map fst Y) = true -> 
  manger_llex.eqSAP A P eqA eqP
  (fold_left (manger_merge_sets_new eqA addP) X
    (manger_merge_sets_new eqA addP Y (au, bu)))
  (fold_left (manger_merge_sets_new eqA addP)
    (filter (λ p : A * P, negb (brel_product eqA eqP p (au, bu))) X)
      (manger_merge_sets_new eqA addP Y (au, bu))) = true.
Proof.
  induction X as [|(ax, bx) X IHx].
  +
    simpl;
    intros * Ha.
    eapply refSAP; try assumption.
  +
    (* induction case *)
    (* case analysis *)
    simpl; intros * Ha.
    case_eq (eqP bx bu);
    case_eq (eqA ax au);
    intros Hb Hc; simpl.
    ++
      specialize (IHx Y au bu Ha).
      eapply trnSAP with 
      (t := (fold_left (manger_merge_sets_new eqA addP) X
      (manger_merge_sets_new eqA addP Y (au, bu))));
      try assumption.
      (* Prove it separately *)
      eapply fold_left_cong_aux_aux_1; 
      try assumption.
      
    ++
      assert (Hd : no_dup eqA (map fst 
          (manger_merge_sets_new eqA addP Y (ax, bx))) = true).
      eapply no_dup_mmsn with (eqP := eqP);
      try assumption.
      specialize (IHx (manger_merge_sets_new eqA addP Y (ax, bx))
      au bu Hd).
      (*
      I can replace 
      (manger_merge_sets_new eqA addP
        (manger_merge_sets_new eqA addP Y (au, bu)) (
        ax, bx))
      by 
      (manger_merge_sets_new eqA addP
        (manger_merge_sets_new eqA addP Y [(au, bu); (ax, bx)]

      Now My goal turns into 
     
      (fold_left (manger_merge_sets_new eqA addP) X
      (manger_merge_sets_new eqA addP Y [(au, bu); (ax, bx)])) =S=
      (fold_left (manger_merge_sets_new eqA addP)
      (filter (λ p : A * P, negb (brel_product eqA eqP p (au, bu))) X)
       (manger_merge_sets_new eqA addP Y [(au, bu); (ax, bx)]))
      After simplification, the goal is same as IHx
      
       *)
      remember ((filter (λ p : A * P, negb 
      (brel_product eqA eqP p (au, bu))) X)) as Xa.
      eapply trnSAP with 
      (t := (fold_left (manger_merge_sets_new eqA addP) X
      (manger_merge_sets_new eqA addP
        (manger_merge_sets_new eqA addP Y (ax, bx)) (au, bu)))); 
        try assumption;
      [eapply fold_left_cong_aux_aux_2; try assumption;
      case_eq (eqA au ax); intro He; try reflexivity;
      rewrite (symA _ _ He) in Hb; congruence| ];
      try assumption.
      eapply trnSAP with 
      (t := (fold_left (manger_merge_sets_new eqA addP) Xa
      (manger_merge_sets_new eqA addP
         (manger_merge_sets_new eqA addP Y (ax, bx)) (au, bu))));
      try assumption.
      eapply fold_left_cong_aux_aux_2;
      try assumption.
      
    ++
      (* easy *)
      (*
      In the goal, 
      (manger_merge_sets_new eqA addP
        (manger_merge_sets_new eqA addP Y (au, bu)) (
        ax, bx)) can be replace by 
      (manger_merge_sets_new eqA addP Y [(au, bu); (ax, bx)])
      *)
      assert (Hd : no_dup eqA (map fst 
        (manger_merge_sets_new eqA addP Y (ax, bx))) = true).
      eapply no_dup_mmsn with (eqP := eqP);
      try assumption.
      specialize (IHx (manger_merge_sets_new eqA addP Y (ax, bx))
      au bu Hd).

      admit.
    ++

      assert (Hd : no_dup eqA (map fst 
        (manger_merge_sets_new eqA addP Y (ax, bx))) = true).
      eapply no_dup_mmsn with (eqP := eqP);
      try assumption.
      specialize (IHx (manger_merge_sets_new eqA addP Y (ax, bx))
      au bu Hd).
      (*
      *)
Admitted.
    






Lemma fold_left_cong_aux_2: 
  forall (X Y : finite_set (A * P)) ax bx, 
  no_dup eqA (map fst Y) = true -> 
  set.in_set (brel_product eqA eqP) X (ax, bx) = true ->
  manger_llex.eqSAP A P eqA eqP
  (fold_left (manger_merge_sets_new eqA addP)
    (filter (λ p : A * P, negb (brel_product eqA eqP p (ax, bx))) X)
      (manger_merge_sets_new eqA addP Y (ax, bx)))
  (fold_left (manger_merge_sets_new eqA addP) X Y) = true.
Proof.
  

Admitted.



(* end admit *)



(*
This is such an awesome proof technique. I have 
never seen it anywhere. This proof requires 
well founded induction with a tricky transitivity. 
*)
Lemma fold_left_cong : 
  forall (U V Y : finite_set (A * P)),
  no_dup eqA (map fst Y) = true -> 
  U =S= V -> 
  fold_left (manger_merge_sets_new eqA addP) U Y =S= 
  fold_left (manger_merge_sets_new eqA addP) V Y.
Proof.
  intro U.
  cut (Acc lt (List.length U)).
  revert U.
  refine (fix Fn U Hacc {struct Hacc} := _).
  refine (match U as xsp return U = xsp -> _ with 
  | [] => _ 
  | (ax, bx) :: Ut => _ 
  end eq_refl); simpl; intros Ha.
  +
    intros * Hb Hc.
    destruct V as [|(av, bv) V]; 
    cbn in Hc |- *;
    [eapply refSAP | congruence];
    try assumption.
  +
    intros * Hb Hc.
    (* get rid of (ax, bx) from U *)
    remember (filter (λ p : A * P, 
      negb (brel_product eqA eqP p (ax, bx))) U) as Urem.
    (* get rid of (ax, bx) from V*)
    remember (filter (λ p : A * P, 
      negb (brel_product eqA eqP p (ax, bx))) V) as Vrem.
    (* Now prove that V is equal to (ax, bx) :: Vrem *)
    assert (Hd : V =S= (ax, bx) :: Vrem).
    rewrite HeqVrem.
    eapply membship_filter; 
    try assumption; exact Hc.
    (* Now prove that Urem =S= Vrem *)
    assert (He : Urem =S= Vrem).
    rewrite HeqUrem, HeqVrem.
    eapply filter_congruence_gen;
    try assumption.
    eapply bop_neg_bProp_product_cong;
    try assumption.
    rewrite <-Ha in Hc;
    exact Hc.
    (* Now prove that it is Accessible relation *)
    assert (Hf : Acc lt (Datatypes.length Urem)).
    eapply Acc_inv with (List.length U);
    [exact Hacc | rewrite HeqUrem, Ha; cbn;
    rewrite refA, refP; cbn; eapply length_filter].
    (* Needs idempotence *)
    assert (Hg : no_dup eqA (map fst 
      (manger_merge_sets_new eqA addP Y (ax, bx))) = true).
    eapply  no_dup_mmsn with (eqP := eqP);
    try assumption.
    specialize (Fn Urem Hf Vrem 
    (manger_merge_sets_new eqA addP Y (ax, bx)) Hg He).
    (* 
      Use transitivity to connect:
      1. (ax, bx) :: Ut to (ax, bx) :: Urem 
      2. (ax, bx) :: Urem to (ax, bx) :: Vrem 
      3. (ax, bx) :: Vrem to V 
    *)
    (* step 1 *)
    eapply trnSAP with 
    (t := fold_left (manger_merge_sets_new eqA addP) 
      ((ax, bx) :: Vrem) Y);
    try assumption.
    (* step 2*)
    eapply trnSAP with 
    (t := (fold_left (manger_merge_sets_new eqA addP) ((ax, bx) :: Urem) Y));
    try assumption.
    (* Now the challenge *)
    ++
      simpl.
      rewrite HeqUrem, Ha;
      simpl; rewrite refA, refP;
      simpl.
      eapply fold_left_cong_aux_1; 
      try assumption.
    ++
      (* How to prove this one? *)
      simpl;
      rewrite HeqVrem.
    (* add an extra assumption (ax, bx) in V *)
    assert (Hi : set.in_set (brel_product eqA eqP) V (ax, bx) = true).
    eapply in_set_left_congruence_v3 with 
    (X := ((ax, bx) :: Vrem));
    [eapply symAP | eapply trnAP | 
    eapply brel_set_symmetric; exact Hd|
    simpl; rewrite refA, refP; simpl; 
    reflexivity]; try assumption.
    eapply fold_left_cong_aux_2;
    try assumption.
  +
    eapply (Wf_nat.well_founded_ltof _ _).
Qed.



Lemma manger_ltrtrans_duplicate_free_forward : 
  forall (X Y Z : finite_set (A * P)) ah bh,
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  no_dup eqA (map fst 
    (fold_left (manger_merge_sets_new eqA addP)
      (ltran_list_product (bop_product mulA mulP) (ah, bh) 
        (fold_left (manger_merge_sets_new eqA addP) X Y)) Z)) = true.
Proof.
  intros * Ha Hb.
  eapply manger_merge_set_no_dup;
  try assumption.
Qed.




Lemma nodup_left_forward : 
  forall (Y : finite_set (A * P)) ah bh,
  no_dup eqA (map fst Y) = true -> 
  no_dup eqA (map fst
    (filter (λ '(s2, _), negb (eqA ah s2)) Y ++
      [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
        (filter (λ '(s2, _), eqA ah s2) Y) (ah, bh)])) = true.
Proof.
  intros * Ha.
  pose proof manger_merge_set_no_dup [(ah, bh)] Y Ha as Hb.
  exact Hb.
Qed.


Lemma manger_ltrtrans_duplicate_free_backward : 
  forall (X Y Z : finite_set (A * P)) ah bh,
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  no_dup eqA (map fst 
    (fold_left (manger_merge_sets_new eqA addP)
      (ltran_list_product (bop_product mulA mulP) 
        (ah, bh) (X ++ Y)) Z)) = true.
Proof.
  intros * Ha Hb.
  eapply manger_merge_set_no_dup;
  try assumption.
Qed.

 
Lemma fold_left_sum_cong : 
  forall (X Y : finite_set P) bh, 
  brel_set eqP X Y = true ->
  eqP 
    (fold_left (λ t1 t2 : P, addP t1 t2) X bh)
    (fold_left (λ t1 t2 : P, addP t1 t2) Y bh) = true.
Proof.
  intros * Ha.
  eapply trnP.
  eapply fold_left_right_symmetric;
  try assumption.
  eapply symP, trnP.
  eapply fold_left_right_symmetric;
  try assumption.
  eapply fold_right_congruence;
  try assumption.
  intros *; eapply symP, addP_assoc.
  intros * Hb Hc.
  eapply cong_addP;
  try assumption.
  exact addP_gen_idempotent.
  eapply brel_set_symmetric; 
  exact Ha.
Qed.

  
(* Trivial but pesky congruence  *)
Lemma fold_left_map_filter_cong :
  forall Y ah bh bh',
  brel_set (brel_product eqA eqP) 
    (filter (λ '(s2, _), eqA ah s2) Y) [(ah, bh')] = true -> 
    eqP
    (fold_left (λ t1 t2 : P, addP t1 t2)
       (map snd (filter (λ '(s2, _), eqA ah s2) Y)) bh) 
    (addP bh bh') = true.
Proof.
  intros * Ha.
  eapply trnP 
  with (t := (fold_left (λ t1 t2 : P, addP t1 t2)
    (map snd [(ah, bh')]) bh)).
  +
   
    eapply fold_left_sum_cong.
    eapply map_preservs_equivalence_on_second with 
    (eqA := eqA);
    try assumption.
  +
    cbn; eapply refP.
Qed.



Lemma set_in_set_in_list_interaction : 
  forall (Y : finite_set (A * P)) a p, 
  set.in_set (brel_product eqA eqP) Y (a, p) = true ->
  in_list eqA (map fst Y) a = true.
Proof.
  induction Y as [|(ya, yb) Y IHy].
  +
    intros * Ha;
    cbn in Ha;
    congruence.
  +
    intros * Ha.
    cbn in Ha |- *.
    case_eq ((eqA a ya)); 
    case_eq ((eqP p yb));
    intros Hb Hc; 
    rewrite Hb, Hc in Ha; 
    cbn in Ha; cbn in Ha |- *;
    try reflexivity.
    eapply IHy; exact Ha.
    eapply IHy; exact Ha.
Qed.


Lemma nodup_inset_set : 
  forall (Y : finite_set (A * P))
  (a : A) (p : P),
  no_dup eqA (map fst Y) = true -> 
  set.in_set (brel_product eqA eqP) Y (a, p) = true ->
  ∃ Y₁ Y₂, 
    set.brel_set (brel_product eqA eqP) Y (Y₁ ++ [(a, p)] ++ Y₂) = true ∧
    (in_list eqA (map fst Y₁) a = false) ∧
    (in_list eqA (map fst Y₂) a = false).
Proof.
  induction Y as [|(ya, yb) Y IHy].
  +
    intros * Ha Hb;
    cbn in Hb; congruence.
  +
    intros * Ha Hb;
    cbn in Hb.
    simpl in Ha. 
    eapply Bool.andb_true_iff in Ha.
    destruct Ha as (Hal & Har).
    eapply Bool.negb_true_iff in Hal.
    case_eq ((and.bop_and (eqA a ya) (eqP p yb)));
    intro Hbt.
    ++
      eapply Bool.andb_true_iff in Hbt.
      destruct Hbt as (Hbl & Hbr).
      exists [], Y.
      cbn; repeat split; try assumption.
      *
        eapply set_equal_with_cons_left;
        try assumption.
        eapply brel_product_intro; 
        [eapply symA | eapply symP]; 
        assumption.
      *
        eapply bop_and_in_list_rewrite with (au := ya);
        try assumption.
    ++
      rewrite Hbt in Hb; cbn in Hb. 
      destruct (IHy _ _ Har Hb) as 
      (Ya & Yb & Yc & Hc & He).
      exists ((ya, yb) :: Ya), Yb.
      cbn; repeat split.
      eapply set_equal_with_cons_right;
      try assumption.
      rewrite Hc.
      (*
        Proof idea:
        We know that ya is not Y 
        Hal : in_list eqA (map fst Y) ya = false 
        We also know that a in Y 
        Yc : 
        brel_set (brel_product eqA eqP) Y (Ya ++ [(a, p)] ++ Yb) = true

      *)

      assert (Hg : in_list eqA (map fst Y) a = true).
      eapply  set_in_set_in_list_interaction; exact Hb.
      rewrite (@bop_and_in_list_rewrite_tricky A 
      eqA symA trnA _ _ _ Hal Hg); reflexivity.
      exact He.
Qed.



Lemma brel_set_not_member_gen : 
  forall (X : finite_set (A * P))  ah, 
  in_list eqA (map fst X) ah = false ->
  brel_set (brel_product eqA eqP) 
    (filter (λ '(s2, _), negb (eqA ah s2)) X) X = true.
Proof.
  induction X as [|(ax, bx) X Ihx].
  +
    intros * Ha;
    cbn; reflexivity.
  +
    intros * Ha.
    simpl in * |- *.
    eapply Bool.orb_false_iff in Ha.
    destruct Ha as (Hal & Har).
    rewrite Hal; simpl.
    specialize (Ihx _ Har).
    eapply set_equal_with_cons_right;
    try assumption.
Qed.


Lemma brel_set_not_member :
  forall (Y₁ Y₂ : finite_set (A * P)) ah,
  in_list eqA (map fst Y₁) ah = false ->
  in_list eqA (map fst Y₂) ah = false ->
  brel_set (brel_product eqA eqP) 
    (filter (λ '(s2, _), negb (eqA ah s2)) (Y₁ ++ Y₂))
    (Y₁ ++ Y₂) = true.
Proof.
  intros * Ha Hb.
  eapply brel_set_not_member_gen.
  rewrite map_app.
  eapply in_list_false_membership; try assumption.
Qed.

 

Lemma bop_list_product_left_cong : 
  forall (U V Y : finite_set (A * P)),
  U =S= V ->
  (bop_list_product_left (bop_product mulA mulP) U Y) =S= 
  (bop_list_product_left (bop_product mulA mulP) V Y).
Proof.
  intros * Ha.
  eapply brel_set_elim_prop in Ha;
  [| eapply symAP | eapply trnAP];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Hb];
  try assumption.
  +
    eapply in_set_list_product_elim in Hb;
    [| eapply refAP | eapply symAP]; try assumption.
    destruct Hb as ((xa, xb) & (ya, yb) & (Hb & Hc) & Hd).
    eapply set.in_set_right_congruence with 
    (a := (bop_product mulA mulP (xa, xb) (ya, yb)));
    [eapply symAP | eapply trnAP | | ];
    try assumption.
    eapply brel_product_elim in Hd;
    destruct Hd as (Hdl & Hdr).
    eapply brel_product_intro;
    [eapply symA | eapply symP ]; 
    try assumption.
    eapply in_set_list_product_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | | exact Hc]; 
    try assumption.
    eapply Ha; exact Hb.
  +
    eapply in_set_list_product_elim in Hb;
    [| eapply refAP | eapply symAP]; try assumption.
    destruct Hb as ((xa, xb) & (ya, yb) & (Hb & Hc) & Hd).
    eapply set.in_set_right_congruence with 
    (a := (bop_product mulA mulP (xa, xb) (ya, yb)));
    [eapply symAP | eapply trnAP | | ];
    try assumption.
    eapply brel_product_elim in Hd;
    destruct Hd as (Hdl & Hdr).
    eapply brel_product_intro;
    [eapply symA | eapply symP ]; 
    try assumption.
    eapply in_set_list_product_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | | exact Hc]; 
    try assumption.
    eapply Ha; exact Hb.
Qed.


Lemma fold_left_bop_list_cong : 
  forall (U V Y Z : finite_set (A * P)),
  U =S= V -> 
  no_dup eqA (map fst Z) = true ->
  fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP) U Y) Z =S= 
  fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP) V Y) Z.
Proof.
  intros * Ha Hb.
  eapply fold_left_cong;
  [exact Hb | eapply bop_list_product_left_cong];
  try assumption.
Qed.



(* rewrite is indeed a pain! *)
(* easy but annonying  *)
Lemma in_set_subst_1 : 
  forall (Yb Y₁ Y₂ Z s2 t : finite_set (A * P)) ah bh bh' x y au av, 
  no_dup eqA (map fst Z) = true ->
  eqA x ah = true ->
  eqP y (addP bh bh') = true ->
  brel_set (brel_product eqA eqP) Yb (Y₁ ++ Y₂) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP)
        (t ++ Yb ++ [(x, y)]) s2) Z) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP)
        (t ++ Y₁ ++ Y₂ ++ [(ah, addP bh bh')]) s2) Z) (au, av) = true.
Proof.
  intros * Ht Ha Hb Hc Hd.
  rewrite <-Hd.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply fold_left_bop_list_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) He];
  try assumption.
  + 
    eapply set.in_set_concat_elim in He;
    [| eapply symAP]; try assumption.
    destruct He as [He | He].
    ++
      eapply set.in_set_concat_intro.
      left; exact He.
    ++
      rewrite app_assoc in He.
      eapply set.in_set_concat_elim in He;
      [| eapply symAP]; try assumption.
      destruct He as [He | He].
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        left.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | ];
        try assumption.
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | eapply brel_set_symmetric];
        try assumption.
        compute; rewrite Ha, Hb, 
        (symA _ _ Ha), (symP _ _ Hb);
        reflexivity.
  +
    eapply set.in_set_concat_elim in He;
    [| eapply symAP]; try assumption.
    destruct He as [He | He].
    ++
      eapply set.in_set_concat_intro.
      left; exact He.
    ++
      eapply set.in_set_concat_elim in He;
      [| eapply symAP]; try assumption.
      destruct He as [He | He].
      +++
        eapply set.in_set_concat_intro.
        right.
        rewrite app_assoc.
        eapply set.in_set_concat_intro.
        left.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | eapply brel_set_symmetric];
        try assumption.
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | eapply brel_set_symmetric];
        try assumption.
        compute; rewrite Ha, Hb, 
        (symA _ _ Ha), (symP _ _ Hb);
        reflexivity.
Qed.



(* easy but annonying  *)
Lemma in_set_subst_2 : 
  forall (Y Y₁ Y₂ s2 Z t : finite_set (A * P)) ah bh bh' au av, 
  no_dup eqA (map fst Z) = true -> 
  brel_set (brel_product eqA eqP) Y (Y₁ ++ [(ah, bh')] ++ Y₂) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP)
      ([(ah, bh)] ++ t ++ Y₁ ++ [(ah, bh')] ++ Y₂) s2) Z) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP)
      ([(ah, bh)] ++ t ++ Y) s2) Z) (au, av) = true.
Proof.
  intros * Ht Ha Hb.
  rewrite <-Hb.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply fold_left_bop_list_cong];
  try assumption.
  (* congruence with ++ *)
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) He];
  try assumption.
  +
    eapply set.in_set_concat_elim in He;
    [| eapply symAP]; try assumption.
    destruct He as [He | He].
    ++
      eapply set.in_set_concat_intro.
      left; exact He.
    ++
      eapply set.in_set_concat_elim in He;
      [| eapply symAP]; try assumption.
      destruct He as [He | He].
      +++
         eapply set.in_set_concat_intro.
         right.
         eapply set.in_set_concat_intro.
         left; exact He.
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | 
        eapply brel_set_symmetric];
        try assumption.
  +
    eapply set.in_set_concat_elim in He;
    [| eapply symAP]; try assumption.
    destruct He as [He | He].
    ++
      eapply set.in_set_concat_intro.
      left; exact He.
    ++
      eapply set.in_set_concat_elim in He;
      [| eapply symAP]; try assumption.
      destruct He as [He | He].
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        left; exact He.
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | ];
        try assumption.
Qed.



(* easy but annonying  *)
Lemma in_set_subst_3 : 
  forall (Y Y₁ Y₂ s2 Z t : finite_set (A * P)) ah bh bh' au av, 
  no_dup eqA (map fst Z) = true ->
  brel_set (brel_product eqA eqP) Y (Y₁ ++ [(ah, bh')] ++ Y₂) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP)
      ([(ah, bh)] ++ t ++ Y) s2) Z) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP)
      ([(ah, bh)] ++ t ++ Y₁ ++ [(ah, bh')] ++ Y₂) s2) Z) (au, av) = true.
Proof.
  intros * Ht Ha Hb.
  rewrite <-Hb.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply fold_left_bop_list_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) He];
  try assumption.
  +
    eapply set.in_set_concat_elim in He;
    [| eapply symAP]; try assumption.
    destruct He as [He | He].
    ++
      eapply set.in_set_concat_intro.
      left; exact He.
    ++
      eapply set.in_set_concat_elim in He;
      [| eapply symAP]; try assumption.
      destruct He as [He | He].
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        left; exact He.
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | ];
        try assumption.
  +
    eapply set.in_set_concat_elim in He;
    [| eapply symAP]; try assumption.
    destruct He as [He | He].
    ++
      eapply set.in_set_concat_intro.
      left; exact He.
    ++
      eapply set.in_set_concat_elim in He;
      [| eapply symAP]; try assumption.
      destruct He as [He | He].
      +++ 
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        left; exact He.
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | eapply brel_set_symmetric];
        try assumption.
Qed.



(* easy but annonying  *)
Lemma in_set_subst_4 : 
  forall (Yb Y₁ Y₂ Z s2 t : finite_set (A * P)) ah bh bh' x y au av, 
  no_dup eqA (map fst Z) = true ->
  eqA x ah = true ->
  eqP y (addP bh bh') = true ->
  brel_set (brel_product eqA eqP) Yb (Y₁ ++ Y₂) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP)
        (t ++ Y₁ ++ Y₂ ++ [(ah, addP bh bh')]) s2) Z) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP)
        (t ++ Yb ++ [(x, y)]) s2) Z) (au, av) = true.
Proof.
  intros * Ht Ha Hb Hc Hd.
  rewrite <-Hd.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply fold_left_bop_list_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) He];
  try assumption.
  +
    eapply set.in_set_concat_elim in He;
    [| eapply symAP]; try assumption.
    destruct He as [He | He].
    ++
      eapply set.in_set_concat_intro.
      left; exact He.
    ++  
      eapply set.in_set_concat_elim in He;
      [| eapply symAP]; try assumption.
      destruct He as [He | He].
      +++
        eapply set.in_set_concat_intro.
        right.
        rewrite app_assoc.
        eapply set.in_set_concat_intro.
        left.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | eapply brel_set_symmetric];
        try assumption.
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | eapply brel_set_symmetric];
        try assumption.
        compute; rewrite Ha, Hb, 
        (symA _ _ Ha), (symP _ _ Hb);
        reflexivity.
  +
    eapply set.in_set_concat_elim in He;
    [| eapply symAP]; try assumption.
    destruct He as [He | He].
    ++
      eapply set.in_set_concat_intro.
      left; exact He.
    ++
      rewrite app_assoc in He.
      eapply set.in_set_concat_elim in He;
      [| eapply symAP]; try assumption.
      destruct He as [He | He].
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        left.
        rewrite <-He.
        eapply in_set_left_congruence_v2;
        [eapply symAP | apply trnAP | ];
        try assumption.
      +++
      eapply set.in_set_concat_intro.
      right.
      eapply set.in_set_concat_intro.
      right.
      rewrite <-He.
      eapply in_set_left_congruence_v2;
      [eapply symAP | apply trnAP | eapply brel_set_symmetric];
      try assumption.
      compute; rewrite Ha, Hb, 
      (symA _ _ Ha), (symP _ _ Hb);
      reflexivity.
Qed.



(* easy but annonying *)
(* congruence and commute *)
Lemma in_set_swap_arugments : 
  forall (t Y₁ Y₂ s2 Z : finite_set (A * P)) au av ah bh bh',
  no_dup eqA (map fst Z) = true -> 
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
     (bop_list_product_left (bop_product mulA mulP)
        (t ++ Y₁ ++ Y₂ ++ [(ah, bh)] ++ [(ah, bh')]) s2) Z) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
     (bop_list_product_left (bop_product mulA mulP)
        ([(ah, bh)] ++ t ++ Y₁ ++ [(ah, bh')] ++ Y₂) s2) Z) (au, av) = true.
Proof.
  intros * Ht Ha.
  rewrite <-Ha.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply fold_left_bop_list_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Hb];
  try assumption.
  +
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption.
    destruct Hb as [Hb | Hb].
    ++  
      eapply set.in_set_concat_intro.
      right.
      eapply set.in_set_concat_intro.
      right. 
      eapply set.in_set_concat_intro.
      right.
      eapply set.in_set_concat_intro.
      left; exact Hb.
    ++
      eapply set.in_set_concat_elim in Hb;
      [| eapply symAP]; try assumption.
      destruct Hb as [Hb | Hb].
      +++
        eapply set.in_set_concat_intro.
        left; exact Hb.
      +++
        eapply set.in_set_concat_elim in Hb;
        [| eapply symAP]; try assumption.
        destruct Hb as [Hb | Hb].
        ++++
          eapply set.in_set_concat_intro.
          right.
          eapply set.in_set_concat_intro.
          left; exact Hb.
        ++++
          eapply set.in_set_concat_elim in Hb;
          [| eapply symAP]; try assumption.
          destruct Hb as [Hb | Hb].
          *
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            right. 
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            right; exact Hb.
          *
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            left; exact Hb.
  +
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption.
    destruct Hb as [Hb | Hb].
    ++
      eapply set.in_set_concat_intro.
      right.
      eapply set.in_set_concat_intro.
      left; exact Hb.
    ++
      eapply set.in_set_concat_elim in Hb;
      [| eapply symAP]; try assumption.
      destruct Hb as [Hb | Hb].
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        left; exact Hb.
      +++
        eapply set.in_set_concat_elim in Hb;
        [| eapply symAP]; try assumption.
        destruct Hb as [Hb | Hb].
        ++++
          eapply set.in_set_concat_intro.
          right.
          eapply set.in_set_concat_intro.
          right. 
          eapply set.in_set_concat_intro.
          right.
          eapply set.in_set_concat_intro.
          right; exact Hb.
        ++++
          eapply set.in_set_concat_elim in Hb;
          [| eapply symAP]; try assumption.
          destruct Hb as [Hb | Hb].
          *
            eapply set.in_set_concat_intro.
            left; exact Hb.
          * 
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            right. 
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            left; exact Hb.
Qed.




(* easy but annonying *)
(* commute and ++ congruence *)
(* indeed annoying *)
Lemma in_set_swap_arugments_2 : 
  forall (t Y₁ Y₂ s2 Z : finite_set (A * P)) au av ah bh bh', 
  no_dup eqA (map fst Z) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
     (bop_list_product_left (bop_product mulA mulP)
        ([(ah, bh)] ++ t ++ Y₁ ++ [(ah, bh')] ++ Y₂) s2) Z) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
     (bop_list_product_left (bop_product mulA mulP)
        (t ++ Y₁ ++ Y₂ ++ [(ah, bh)] ++ [(ah, bh')]) s2) Z) (au, av) = true.
Proof.
  intros * Ht Ha.
  rewrite <-Ha.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply fold_left_bop_list_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Hb];
  try assumption.
  +
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption.
    destruct Hb as [Hb | Hb].
    ++
      eapply set.in_set_concat_intro.
      right.
      eapply set.in_set_concat_intro.
      left. exact Hb.
    ++
      eapply set.in_set_concat_elim in Hb;
      [| eapply symAP]; try assumption.
      destruct Hb as [Hb | Hb].
      +++
        eapply set.in_set_concat_intro.
        right.
        eapply set.in_set_concat_intro.
        right. 
        eapply set.in_set_concat_intro.
        left; exact Hb.
      +++
        eapply set.in_set_concat_elim in Hb;
        [| eapply symAP]; try assumption.
        destruct Hb as [Hb | Hb].
        ++++
          eapply set.in_set_concat_intro.
          right.
          eapply set.in_set_concat_intro.
          right. 
          eapply set.in_set_concat_intro.
          right.
          eapply set.in_set_concat_intro.
          right; exact Hb.
        ++++
          eapply set.in_set_concat_elim in Hb;
          [| eapply symAP]; try assumption.
          destruct Hb as [Hb | Hb].
          *
            eapply set.in_set_concat_intro.
            left; exact Hb.
          *
          eapply set.in_set_concat_intro.
          right.
          eapply set.in_set_concat_intro.
          right. 
          eapply set.in_set_concat_intro.
          right.
          eapply set.in_set_concat_intro.
          left; exact Hb.
  +
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption.
    destruct Hb as [Hb | Hb].
    ++
      eapply set.in_set_concat_intro.
      right.
      eapply set.in_set_concat_intro.
      right. 
      eapply set.in_set_concat_intro.
      right.
      eapply set.in_set_concat_intro.
      left. exact Hb.
    ++  
      eapply set.in_set_concat_elim in Hb;
      [| eapply symAP]; try assumption.
      destruct Hb as [Hb | Hb].
      +++
        eapply set.in_set_concat_intro.
        left. exact Hb.
      +++
        eapply set.in_set_concat_elim in Hb;
        [| eapply symAP]; try assumption.
        destruct Hb as [Hb | Hb].
        ++++
          eapply set.in_set_concat_intro.
          right.
          eapply set.in_set_concat_intro.
          left. exact Hb.
        ++++
          eapply set.in_set_concat_elim in Hb;
          [| eapply symAP]; try assumption.
          destruct Hb as [Hb | Hb].
          *
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            right. 
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            right; exact Hb.
          *
            eapply set.in_set_concat_intro.
            right.
            eapply set.in_set_concat_intro.
            right. 
            eapply set.in_set_concat_intro.
            left. exact Hb.
Qed.
      




Lemma set_in_swap_first_step : 
  forall (Xa Xb Y : finite_set (A * P)) ah bh au av, 
  no_dup eqA (map fst Y) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    ((ah, bh) :: Xb ++ Xa) Y) (au, av) = true->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    (Xa ++ (ah, bh) :: Xb) Y) (au, av) = true.
Proof.
  intros * Ht Ha.
  rewrite <-Ha.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply  fold_left_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Hb];
  try assumption.
  +
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption.
    rewrite app_comm_cons.
    eapply set.in_set_concat_intro.
    destruct Hb as [Hb | Hb];
    [right | left]; assumption.
  +
    rewrite app_comm_cons in Hb.
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption.
    eapply set.in_set_concat_intro.
    destruct Hb as [Hb | Hb];
    [right | left]; assumption.
Qed.


Lemma set_in_swap_second_step : 
  forall (Xa Xb Y : finite_set (A * P)) au av, 
  no_dup eqA (map fst Y) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP) (Xa ++ Xb) Y) 
  (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP) (Xb ++ Xa) Y) 
  (au, av) = true.
Proof.
  intros * Ht Ha.
  rewrite <-Ha.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply  fold_left_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Hb];
  try assumption.
  +
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption;
    eapply set.in_set_concat_intro.
    destruct Hb as [Hb | Hb];
    [right | left]; assumption.
  +
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption;
    eapply set.in_set_concat_intro.
    destruct Hb as [Hb | Hb];
    [right | left]; assumption.
Qed.


Lemma set_in_swap_third_step : 
  forall (Xa Xb Y : finite_set (A * P)) ah bh au av, 
  no_dup eqA (map fst Y) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    (Xa ++ (ah, bh) :: Xb) Y) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    ((ah, bh) :: Xb ++ Xa) Y) (au, av) = true.
Proof.
  intros * Ha Hb.
  rewrite <-Hb.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply  fold_left_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Hc];
  try assumption.
  +
    rewrite app_comm_cons in Hc.
    eapply set.in_set_concat_elim in Hc;
    [| eapply symAP]; try assumption;
    eapply set.in_set_concat_intro.
    destruct Hc as [Hc | Hc];
    [right | left]; assumption.
  +
    eapply set.in_set_concat_elim in Hc;
    [| eapply symAP]; try assumption.
    rewrite app_comm_cons.
    eapply set.in_set_concat_intro.
    destruct Hc as [Hc | Hc];
    [right | left]; assumption.
Qed.



(* Move this to manger_sets.v *)
Lemma manger_congruence_accumulator : 
  forall (Y : finite_set (A * P)) ah bh,
  ah == bh ->
  manger_merge_sets_new eqA addP Y ah =S= 
  manger_merge_sets_new eqA addP Y bh.
Proof.
  induction Y as [|(ya, yb) Y IHy];
  intros (aha, ahb) (bha, bhb) Ha.
  eapply brel_product_elim in Ha.
  destruct Ha as (Hal & Har).
  +
    cbn.
    eapply brel_set_intro_prop;
    [eapply refAP | split; intros (ax, bx) Hb];
    try assumption.
    *
      cbn in Hb |- *.
      case_eq (eqA ax aha);
      case_eq (eqP bx ahb);
      intros Hc Hd;
      rewrite Hc, Hd in Hb;
      cbn in Hb |- *;
      try congruence.
      rewrite (trnA _ _ _ Hd Hal).
      rewrite (trnP _ _ _ Hc Har).
      reflexivity.
    *
      cbn in Hb |- *.
      case_eq (eqA ax bha);
      case_eq (eqP bx bhb);
      intros Hc Hd;
      rewrite Hc, Hd in Hb;
      cbn in Hb |- *;
      try congruence.
      rewrite (trnA _ _ _ Hd (symA _ _ Hal)).
      rewrite (trnP _ _ _ Hc (symP _ _ Har)).
      reflexivity.
  +
    eapply brel_product_elim in Ha.
    destruct Ha as (Hal & Har).
    cbn.
    (* Provable but annoying *)
    case_eq (eqA aha ya);
    case_eq ((eqA bha ya));
    intros Hc Hd; 
    cbn.
    ++
      eapply (IHy (aha, addP ahb yb) (bha, addP bhb yb)).
      eapply brel_product_intro.
      exact (trnA _ _ _ Hd (symA _ _ Hc)).
      eapply cong_addP;
      [exact Har | eapply refP].
    ++
      (* false *)
      rewrite (trnA _ _ _ (symA _ _ Hal) Hd) in Hc;
      congruence. 
    ++
      (* false *)
      rewrite (trnA _ _ _ Hal Hc) in Hd;
      congruence.
    ++
      eapply set_equal_with_cons_right;
      try assumption.
      eapply (IHy (aha, ahb) (bha, bhb)).
      eapply brel_product_intro.
      exact Hal. exact Har.
Qed.


(* Important Lemma so prove it first *)
(* I can assume that Y is no duplicate but I think, right 
now, I don't need it
*)
(* Challenging *)
(* requires right distributivity *)
Lemma set_in_fold_dist_imp : 
  forall (X Y : finite_set (A * P)) au av ah bh bh', 
  no_dup eqA (map fst Y) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP)
        [(ah, addP bh bh')] X) Y) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP)
        ([(ah, bh)] ++ [(ah, bh')]) X) Y) (au, av) = true.
Proof.
  induction X as [|(ax, bx) X IHx].
  +
    cbn; intros; 
    assumption.
  +
    simpl; intros * Ha Hb.
    simpl in IHx.
    rewrite app_nil_r in Hb |- *.
    specialize (IHx (manger_merge_sets_new eqA addP Y
     (mulA ah ax, mulP (addP bh bh') bx)) au av ah bh bh').
    assert (Hc : no_dup eqA
      (map fst (manger_merge_sets_new eqA addP Y
        (mulA ah ax, mulP (addP bh bh') bx))) = true).
    eapply no_dup_mmsn with (eqP := eqP);
    try assumption.
    specialize (IHx Hc); clear Hc.
    rewrite app_nil_r in IHx.
    specialize (IHx Hb); clear Hb.
    (* Now using IHx, discharge the goal *)
    rewrite app_nil_r in IHx.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh) X)
    as Xa.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh') X)
    as Xb.
    eapply set_in_swap_first_step;
    [eapply no_dup_mmsn with (eqP := eqP) | simpl];
    try assumption.
    remember (mulA ah ax) as ahax.
    remember (mulP bh bx) as bhbx.
    remember (mulP bh' bx) as bhbx'.
    eapply set_in_swap_second_step.
    eapply no_dup_mmsn with (eqP := eqP);
    try assumption.
    eapply no_dup_mmsn with (eqP := eqP);
    try assumption.
    eapply fold_left_in_set_mmsn_cong with 
    (V := (manger_merge_sets_new eqA addP Y 
    (ahax, mulP (addP bh bh') bx))); 
    try assumption.
    exact addP_gen_idempotent.
    subst.
    (* I need distributivity 
      eqP (mulP (addP bh bh') bx) 
      (addP (mulP bh bx) (addP bh' bx)) = true
    *)
    eapply brel_set_transitive with
    (t :=  (manger_merge_sets_new eqA addP Y 
      (mulA ah ax, addP (mulP bh bx) (mulP bh' bx))));
    [eapply refAP | eapply symAP | eapply trnAP | | ];
    try assumption.
    ++
      eapply  manger_congruence_accumulator,
      brel_product_intro;
      [eapply refA | 
      eapply mulP_addP_right_distributive].
    ++
      eapply brel_set_symmetric.
      eapply  mmsn_same_add with 
      (zeroP := zeroP); try assumption.
      eapply refA.
Qed.

    

(* Challenging *)
Lemma set_in_fold_dist_imp_2 : 
  forall (X Y : finite_set (A * P)) au av ah bh bh', 
  no_dup eqA (map fst Y) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP)
        ([(ah, bh)] ++ [(ah, bh')]) X) Y) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP)
        [(ah, addP bh bh')] X) Y) (au, av) = true.
Proof.
  induction X as [|(ax, bx) X IHx].
  +
    cbn; intros; 
    assumption.
  +
    simpl; intros * Ha Hb.
    simpl in IHx.
    rewrite app_nil_r in Hb |- *.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh) X)
    as Xa.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh') X)
    as Xb.
    (* message Hb *)
    eapply set_in_swap_third_step in Hb;
    [| eapply no_dup_mmsn with (eqP := eqP)];
    try assumption.
    simpl in Hb.
    eapply set_in_swap_second_step in Hb;
    [|eapply no_dup_mmsn with (eqP := eqP); 
      try assumption; 
      eapply no_dup_mmsn with (eqP := eqP)];
    try assumption.

    specialize (IHx (manger_merge_sets_new eqA addP
      (manger_merge_sets_new eqA addP Y (mulA ah ax, mulP bh bx))
      (mulA ah ax, mulP bh' bx)) au av ah bh bh').
    assert (Hc : no_dup eqA (map fst
      (manger_merge_sets_new eqA addP
        (manger_merge_sets_new eqA addP Y (mulA ah ax, mulP bh bx))
        (mulA ah ax, mulP bh' bx))) = true).
    eapply no_dup_mmsn with (eqP := eqP); 
    try assumption; 
    eapply no_dup_mmsn with (eqP := eqP); try assumption.
    repeat rewrite app_nil_r in IHx.
    subst.
    specialize (IHx Hc Hb);
    clear Hb Hc.
    eapply fold_left_in_set_mmsn_cong with 
    (V := (manger_merge_sets_new eqA addP
    (manger_merge_sets_new eqA addP Y (mulA ah ax, mulP bh bx))
    (mulA ah ax, mulP bh' bx)));
    try assumption.
    exact addP_gen_idempotent.
    eapply brel_set_transitive with 
    (t := manger_merge_sets_new eqA addP Y 
    (mulA ah ax, addP (mulP bh bx) (mulP bh' bx)));
    [eapply refAP | eapply symAP | eapply trnAP | |];
    try assumption.
    ++
      eapply  mmsn_same_add with 
      (zeroP := zeroP); try assumption.
      eapply refA.
    ++
      eapply  manger_congruence_accumulator,
      brel_product_intro;
      [eapply refA | eapply symP,
      mulP_addP_right_distributive].
Qed.





Lemma set_in_fold_left_swap_2 : 
  forall (tY tX s2 Z : finite_set (A * P)) au av, 
  no_dup eqA (map fst Z) = true -> 
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP)
      (tX ++ tY) s2) Z) (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
  (fold_left (manger_merge_sets_new eqA addP)
     (bop_list_product_left (bop_product mulA mulP)
        (tY ++ tX) s2) Z) (au, av) = true.
Proof.
  intros * Ht Ha.
  rewrite <-Ha.
  eapply in_set_left_congruence_v2;
  [eapply symAP | eapply trnAP | eapply fold_left_bop_list_cong];
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Hb];
  try assumption.
  + 
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption.
    eapply set.in_set_concat_intro.
    destruct Hb as [Hb | Hb]; 
    [right | left]; assumption.
  +
    eapply set.in_set_concat_elim in Hb;
    [| eapply symAP]; try assumption.
    eapply set.in_set_concat_intro.
    destruct Hb as [Hb | Hb]; 
    [right | left]; assumption.
Qed.

(* begin admit *)
(* If I replace =S= by =, then it is true? 
Try with some examples!
Chellenging
*)
Lemma fold_left_ltrtrans_interaction : 
  forall s2 Y Z ah bh,
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true -> 
  fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (ah, bh)
      (fold_left (manger_merge_sets_new eqA addP) s2 Y)) Z =S=
  fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (ah, bh) (s2 ++ Y)) Z.
Proof.
Admitted.  

(* end of admit *)



Lemma bop_list_product_left_app : 
  forall (X Y Z : finite_set (A * P)),
  (bop_list_product_left (bop_product mulA mulP) (X ++ Y) Z) =
  (bop_list_product_left (bop_product mulA mulP) X Z) ++
  (bop_list_product_left (bop_product mulA mulP) Y Z).
Proof.
  induction X as [|(ax, bx) X Ihx].
  +
    cbn; intros; reflexivity.
  +
    cbn; intros *.
    rewrite Ihx.
    rewrite app_assoc.
    reflexivity.
Qed.


Lemma bop_list_product_left_swap_list : 
  forall (X Y Z : finite_set (A * P)),
  (bop_list_product_left (bop_product mulA mulP)
    (X ++ Y) Z) =S= 
  (bop_list_product_left (bop_product mulA mulP)
    (Y ++ X) Z).
Proof.
  intros *.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Ha];
  try assumption.
  +
    rewrite bop_list_product_left_app in Ha |- *.
    eapply set.in_set_concat_elim in Ha;
    [eapply set.in_set_concat_intro | eapply symAP];
    try assumption.
    destruct Ha as [Ha | Ha];
    [right | left]; try assumption.
  +
    rewrite bop_list_product_left_app in Ha |- *.
    eapply set.in_set_concat_elim in Ha;
    [eapply set.in_set_concat_intro | eapply symAP];
    try assumption.
    destruct Ha as [Ha | Ha];
    [right | left]; try assumption.
Qed.


Lemma fold_left_manger_merge_set_idempotent : 
  forall (X Y : finite_set (A * P)),
  no_dup eqA (map fst Y) = true -> 
  fold_left (manger_merge_sets_new eqA addP)
    (set.uop_duplicate_elim (brel_product eqA eqP) X) Y =S= 
  fold_left (manger_merge_sets_new eqA addP) X Y.
Proof.
  (* Use the above two lemmas to finish the proof 
    I think above two lemmas should exists some where! 
  *)
  intros * Ha.
  eapply fold_left_cong, uop_dup_elim_membership_cong;
  assumption.
Qed.

Lemma bop_congruecen_eqA : 
  forall ah,
  theory.bProp_congruence (A * P) (brel_product eqA eqP)
  (λ '(s2, _), eqA ah s2).
Proof.
  intros ? (xa, xb) (ya, yb) Hx.
  eapply brel_product_elim in Hx.
  destruct Hx as (Hxl & Hxr).
  case_eq (eqA ah xa);
  case_eq (eqA ah ya);
  intros Ha Hb;
  try reflexivity.
  rewrite (trnA _ _ _ Hb Hxl) in Ha;
  congruence.
  apply symA in Hxl.
  rewrite (trnA _ _ _ Ha Hxl) in Hb;
  congruence.
Qed.

Lemma ltr_bop_list_dist : 
  forall (tY s2 : finite_set (A * P)) ah bh, 
  (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
   bop_list_product_left (bop_product mulA mulP) tY s2) =
  (bop_list_product_left (bop_product mulA mulP) 
     ([(ah, bh)] ++ tY ) s2).
Proof.
  intros *; cbn; reflexivity.
Qed.



(* This proof existed somewhere in algorithm directory 
but I can't find it. *)
Lemma filter_in_set_no_dup : 
  forall (Y Y₁ Y₂ : finite_set (A * P)) ah bh', 
  brel_set (brel_product eqA eqP) Y
    (Y₁ ++ [(ah, bh')] ++ Y₂) = true ->
  in_list eqA (map fst Y₁) ah = false ->
  in_list eqA (map fst Y₂) ah = false ->
  filter (λ '(s2, _), eqA ah s2) Y =S= [(ah, bh')] ∧
  filter (λ '(s2, _), negb (eqA ah s2)) Y =S= Y₁ ++ Y₂.
Proof.
  intros * Ha Hb Hc.
  split.
  +
    eapply trnSAP with  
    (t := filter (λ '(s2, _), eqA ah s2)  (Y₁ ++ [(ah, bh')] ++ Y₂)); try 
    assumption.
    eapply filter_congruence_gen; try assumption.
    eapply bop_congruecen_eqA.
    rewrite <-list_filter_lib_filter_same;
    repeat rewrite filter_app.
    cbn; rewrite refA.
    pose proof filter_not_in_set_no_dup Y₁ ah Hb as Hd;
    destruct Hd as (Hdl & Hdr).
    pose proof filter_not_in_set_no_dup Y₂ ah Hc as He;
    destruct He as (Hel & Her).
    repeat rewrite list_filter_lib_filter_same.
    rewrite Hdl, Hel; cbn.
    eapply refSAP; try assumption.
  +
    eapply trnSAP with  
    (t := filter (λ '(s2, _), negb (eqA ah s2))  (Y₁ ++ [(ah, bh')] ++ Y₂)); try 
    assumption.
    eapply filter_congruence_gen; try assumption.
    eapply bop_theory_bProp_congruence_negb; try assumption.
    rewrite <-list_filter_lib_filter_same;
    repeat rewrite filter_app.
    cbn; rewrite refA; cbn.
    pose proof filter_not_in_set_no_dup Y₁ ah Hb as Hd;
    destruct Hd as (Hdl & Hdr).
    pose proof filter_not_in_set_no_dup Y₂ ah Hc as He;
    destruct He as (Hel & Her).
    repeat rewrite list_filter_lib_filter_same.
    rewrite Hdr, Her; cbn.
    eapply refSAP; try assumption.
Qed.

   





Lemma no_dup_split_list_aux : 
  forall (Y : finite_set (A * P)) ah,
  no_dup eqA (map fst Y) = true ->
  set.in_set eqA (map fst Y) ah = true ->
  ∃ bh, set.in_set (manger_llex.eqAP A P eqA eqP) Y (ah, bh) = true.
Proof.
  induction Y as [|(ax, bx) Y IHy].
  +
    cbn; intros; 
    try congruence. 
  +
    cbn; intros * Ha Hb.
    eapply and.bop_and_elim in Ha;
    destruct Ha as (Hal & Har);
    eapply Bool.negb_true_iff in Hal.
    case_eq ((eqA ah ax)); intro Hc.
    *
      exists bx. rewrite refP;
      cbn; reflexivity.
    * 
      rewrite Hc in Hb; 
      simpl in Hb.
      destruct (IHy _ Har Hb) as (bh' & Hd).
      exists bh'.
      rewrite Hd; cbn; 
      reflexivity.
Qed.





Lemma ltran_list_product_cong : 
  forall (X Y : finite_set (A * P)) ah bh, 
  X =S= Y ->
  ltran_list_product (bop_product mulA mulP) (ah, bh) X =S= 
  ltran_list_product (bop_product mulA mulP) (ah, bh) Y.
Proof.
  intros * Ha.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Hb];
  try assumption.
  +
    eapply in_set_ltran_list_product_elim in Hb;
    [|eapply refAP | eapply symAP]; try assumption.
    destruct Hb as ((ya, yb) & Hb & Hc).
    (* replace (ax, bx) in the goal with goal with Hc. *)
    eapply set.in_set_right_congruence with 
      (a := (bop_product mulA mulP (ah, bh) (ya, yb)));
    [eapply symAP | eapply trnAP | eapply symAP | ];
    try assumption.
    eapply in_set_ltran_list_product_intro;
    [eapply refAP | eapply symAP | eapply bop_cong | ];
    try assumption.
    eapply brel_set_elim_prop in Ha;
    [| eapply symAP | eapply trnAP];
    try assumption.
    destruct Ha as (Hal & Har).
    eapply Hal; try assumption.

  +
    eapply in_set_ltran_list_product_elim in Hb;
    [|eapply refAP | eapply symAP]; try assumption.
    destruct Hb as ((ya, yb) & Hb & Hc).
    eapply set.in_set_right_congruence with 
      (a := (bop_product mulA mulP (ah, bh) (ya, yb)));
    [eapply symAP | eapply trnAP | eapply symAP | ];
    try assumption.
    eapply in_set_ltran_list_product_intro;
    [eapply refAP | eapply symAP | eapply bop_cong | ];
    try assumption.
    eapply brel_set_elim_prop in Ha;
    [| eapply symAP | eapply trnAP];
    try assumption.
    destruct Ha as (Hal & Har).
    eapply Har; try assumption.
Qed.
    



Lemma bop_left_uop_inv_phase_1_gen_forward : 
  forall (s1 s2 Y Z : finite_set (A * P)) au av, 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP
        (fold_left (manger_merge_sets_new eqA addP) s1 Y) s2) Z) 
        (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP (s1 ++ Y) s2) Z) 
      (au, av) = true.
Proof.
  (* Don't touch s2 *)
  (* Also, don't use fold_left *)
  refine (fix Fn s1 := 
    match s1 as s1' return s1 = s1' -> _ with 
    | [] => _ 
    | (ah, bh) :: t => _ 
    end eq_refl).
  +
    intros Ha * Hb Hc Hd.
    cbn in Hd |- *.
    exact Hd.
  +
    intros Ha * Hb Hc Hd;
    cbn in Hd |- *.
    (* Looks complicated but looks provable *)
    (* elim set.uop_duplicate_elim *)
    unfold manger_product_phase_0, bop_lift in Fn.
    specialize (Fn t s2  (filter (λ '(s2, _), negb (eqA ah s2)) Y 
      ++ [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
        (filter (λ '(s2, _), eqA ah s2) Y) (ah, bh)]) Z au av
    (nodup_left_forward Y ah bh Hb) Hc Hd).
    clear Hd.
    remember ([fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA ah s2) Y) (ah, bh)]) as Ya.
    remember (filter (λ '(s2, _), negb (eqA ah s2)) Y) as Yb.
    (* Now the challenge is to show that the goal holds from Fn *)
    (* Get rid of set.uop_duplicate_elim from Fn   *)
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP) (t ++ Yb ++ Ya) s2) Z)
    in Fn;
    [ | eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    (* Get rid of set.uop_duplicate_elim from the goal *)
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP) 
    (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
    bop_list_product_left (bop_product mulA mulP) (t ++ Y) s2) Z);
    [|eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    (* bloody hell!!! This is going to be a nightmare *)
    (* proof sketch 
      ah ∉ (map fst Y) ∨ ah ∈ (map fst Y) (* there are no duplicates in Y*)
      1.  ah ∉ (map fst Y)
        Ya = [(ah, bh)] 
        Yb = Y 
        And we are home! 

      2. ah ∈ (map fst Y)
        Y =S= [(ah, bh')] ++ Yt (* no ah in Yt *)

        Ya := [(ah, bh + bh')]
        Yb = Yt 


        Fn :
        set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
          (bop_list_product_left (bop_product mulA mulP)
          (t ++ Yb ++ [(ah, bh + bh')]) s2) Z) (au, av) = true


        2.1 Simplify Fn:
        set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
        (ltran_list_product (bop_product mulA mulP)
          (ah, bh + bh') s2 ++ 
          (bop_list_product_left (bop_product mulA mulP)
            (t ++ Yb) s2) Z) (au, av) = true

        2.2 Use fold_left_app in Fn:
        set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
        (bop_list_product_left (bop_product mulA mulP) (t ++ Yb) s2)
        (fold_left (manger_merge_sets_new eqA addP)
          (ltran_list_product (bop_product mulA mulP) (ah, bh + bh') s2) 
        Z) (au, av) = true


        2.3 Rewrite Y in goal. 
        set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
          (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
            ltran_list_product (bop_product mulA mulP) (ah, bh') s2 ++ 
            bop_list_product_left (bop_product mulA mulP) (t ++ Yb) s2) Z)
        (au, av) = true
      
        2.4 Use fold_left_app in step 2.3 
        set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
          (bop_list_product_left (bop_product mulA mulP) (t ++ Yb) s2) Z) 
          (fold_left (manger_merge_sets_new eqA addP) 
            (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
            ltran_list_product (bop_product mulA mulP) (ah, bh') s2) 
          Z)) (au, av) = true


        Now just prove that 
        (fold_left (manger_merge_sets_new eqA addP)
          (ltran_list_product (bop_product mulA mulP) (ah, bh + bh') s2) Z) 
        =S=
        (fold_left (manger_merge_sets_new eqA addP) 
            (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
            ltran_list_product (bop_product mulA mulP) (ah, bh') s2) 
        Z)
        We are home! 
        I have the proof! 
    *)
    case_eq (set.in_set eqA (map fst Y) ah);
    intro Hd; swap 1 2.
    ++
      destruct (filter_not_in_set_no_dup Y ah Hd) as (Hel & Her).
      rewrite Hel in HeqYa;
      cbn in HeqYa.
      rewrite Her in HeqYb.
      rewrite HeqYa, 
      HeqYb in Fn.
      rewrite ltr_bop_list_dist.
      rewrite <-Fn.
      eapply in_set_left_congruence_v2;
      [eapply symAP | eapply trnAP | ];
      try assumption.
      remember (t ++ Y) as tY.
      rewrite app_assoc.
      rewrite <-HeqtY.
      eapply fold_left_cong;
      [exact Hc | eapply bop_list_product_left_swap_list].
    ++
      (* challenging case! *)
      (*
       ah ∈ (map fst Y)
        Y =S= [(ah, bh')] ++ Yt (* no ah in Yt *)

        Ya := [(ah, bh + bh')]
        Yb = Yt 
      *)

      destruct (no_dup_split_list_aux Y ah Hb Hd) as 
      (bh' & He).
      destruct (nodup_inset_set Y ah bh' Hb He)
      as (Y₁ & Y₂ & Hf & Hg & Hi).
      rewrite ltr_bop_list_dist.
      destruct (manger_merge_set_new_aux_congruence_left
      A P eqA eqP refA symA trnA refP symP trnP 
      Y (Y₁ ++ [(ah, bh')] ++ Y₂) ah Hf) as (Hjl & Hjr).
      repeat rewrite <- list_filter_lib_filter_same in Hjl, Hjr.
      repeat rewrite filter_app in Hjl, Hjr.
      cbn in Hjl, Hjr;
      rewrite refA in Hjl, Hjr;
      cbn in Hjl, Hjr.
      pose proof (in_list_filter_empty A P eqA symA Y₁ ah Hg) as Hk.
      erewrite <-filter_arg_swap_gen with (ax := ah) in Hk;
      try assumption; try (eapply refA).
      rewrite Hk in Hjr; clear Hk.
      pose proof (in_list_filter_empty A P eqA symA Y₂ ah Hi) as Hk.
      erewrite <-filter_arg_swap_gen with (ax := ah) in Hk;
      try assumption; try (eapply refA).
      rewrite Hk in Hjr; clear Hk.
      cbn in Hjr.
      rewrite <-filter_app in Hjl.
      repeat rewrite list_filter_lib_filter_same in Hjl, Hjr.
      rewrite list_filter_lib_filter_same in Hjl.
      (* How to replace 
      1. I want to replace Y in the goal by 
        Y₁ ++ [(ah, bh)] ++ Y₂ 

        Yb by Y₁ ++ Y₂  and 
        Ya by [(ah, bh + bh')] in Fn

        Fn 
      *)
      assert (Hk : fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA ah s2) Y) (ah, bh) == 
      (ah, fold_left (λ t1 t2 : P, addP t1 t2) 
      (map snd (List.filter (λ '(x, _), eqA ah x) Y)) bh)).
      eapply fold_left_filter; try assumption.
      destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA ah s2) Y) (ah, bh)) as (x, y) eqn:Hl.
      eapply brel_product_elim in Hk.
      destruct Hk as [Hkl Hkr].
      rewrite <-HeqYb in Hjl.
      rewrite HeqYa in Fn.
      rewrite list_filter_lib_filter_same in Hkr.
      assert (Hm : eqP y (addP bh bh') = true).
      eapply trnP with (fold_left (λ t1 t2 : P, addP t1 t2)
      (map snd (filter (λ '(x, _), eqA ah x) Y)) bh);
      [exact Hkr | ].
      eapply trnP with 
      (fold_left (λ t1 t2 : P, addP t1 t2)
      (map snd (filter (λ '(x0, _), eqA ah x0) [(ah, bh')])) bh).
      cbn; rewrite refA; cbn.
      (* Prove it separately. It's polluting the main proof *)
      eapply fold_left_map_filter_cong; try assumption.
      cbn; rewrite refA; cbn; eapply refP.
      clear Hkr Hl.
      (* Yb = Y₁ ++ Y₂ *)
      assert (Hn : brel_set (brel_product eqA eqP) Yb (Y₁ ++ Y₂) = true).
      eapply brel_set_transitive with 
      (t := (filter (λ '(s2, _), negb (eqA ah s2)) (Y₁ ++ Y₂)));
      [eapply refAP | eapply symAP | eapply trnAP | 
      exact Hjl |]; try assumption.
      eapply brel_set_not_member; try assumption.
      clear Hjl Hjr.
      pose proof in_set_subst_1 Yb Y₁ Y₂ Z s2 t ah bh bh' x y au av
      Hc Hkl Hm Hn Fn as Fnn.
      eapply in_set_subst_2;
      [| exact Hf | ]; try assumption.
      rewrite app_assoc in Fnn.
      rewrite app_assoc in Fnn.

      (* Now the next challenge is infer the goal from Fnn *)
      remember ((t ++ Y₁) ++ Y₂) as tY.
      eapply in_set_swap_arugments; 
      try assumption.
      rewrite app_assoc, app_assoc.
      rewrite <-HeqtY.

      (*This lemma is going to be challengign *)
      rewrite bop_list_product_left_app in Fnn |- *.
      remember (bop_list_product_left (bop_product mulA mulP) tY s2) as tYX.
      rewrite fold_left_app in Fnn |- *.
      remember (fold_left (manger_merge_sets_new eqA addP) tYX Z) as ftYX.
      eapply  set_in_fold_dist_imp; try assumption.
      subst; eapply manger_merge_set_no_dup; 
      try assumption.
Qed.





Lemma bop_left_uop_inv_phase_1_gen_backward : 
  forall (s1 s2 Y Z : finite_set (A * P)) au av, 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP (s1 ++ Y) s2) Z) 
      (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP
        (fold_left (manger_merge_sets_new eqA addP) s1 Y) s2) Z) 
        (au, av) = true.
Proof.
  (* Going to be very similar to above *)
  (* Don't touch s2 *)
  (* Also, don't use fold_left *)
  refine (fix Fn s1 := 
    match s1 as s1' return s1 = s1' -> _ with 
    | [] => _ 
    | (ah, bh) :: t => _ 
    end eq_refl).
  +
    intros Ha * Hb Hc Hd.
    cbn in Hd |- *.
    exact Hd.
  +
    intros Ha * Hb Hc Hd;
    cbn in Hd |- *.
    unfold manger_product_phase_0, bop_lift in Fn.
    (* Now think for what do we want to instantiate *)
    remember ([fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA ah s2) Y) (ah, bh)]) as Ya.
    remember (filter (λ '(s2, _), negb (eqA ah s2)) Y) as Yb.
    eapply Fn;
    [subst; eapply nodup_left_forward; try assumption | 
    exact Hc | ].
    (* Get rid of set.uop_duplicate_elim from Fn   *)
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP) (t ++ Yb ++ Ya) s2) Z);
    [ | eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    (* Get rid of set.uop_duplicate_elim from the goal *)
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP) 
    (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
    bop_list_product_left (bop_product mulA mulP) (t ++ Y) s2) Z) in Hd;
    [|eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    clear Fn.
    (* Now do the same trick as the previous one *)
    (*
    
    proof sketch 
      ah ∉ (map fst Y) ∨ ah ∈ (map fst Y) (* there are no duplicates in Y*)
      1.  ah ∉ (map fst Y)
        Ya = [(ah, bh)] 
        Yb = Y 
        And we are home! 

      2. ah ∈ (map fst Y)
        Y =S= [(ah, bh')] ++ Yt (* no ah in Yt *)

        Ya := [(ah, bh + bh')]
        Yb = Yt 

        2.1 Rewrite Y in Hd. 
        Hd: set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
          (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
           bop_list_product_left (bop_product mulA mulP) 
            (t ++ [(ah, bh')] ++ Yb) s2) Z) (au, av) = true

        2.2 Simplify Hd (pull out ah and bh')
        Hd : set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
          (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
          ltran_list_product (bop_product mulA mulP) (ah, bh') s2 ++
           bop_list_product_left (bop_product mulA mulP) 
            (t  ++ Yb) s2) Z) (au, av) = true
        2.4 Rewrite fold_left_app in Hd
          set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
           (bop_list_product_left (bop_product mulA mulP) 
            (t  ++ Yb) s2) 
          (fold_left (manger_merge_sets_new eqA addP)
          ((ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
          ltran_list_product (bop_product mulA mulP) (ah, bh') s2) Z) (au, av) = true



        2.5 Rewrite Ya in goal:
        set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
        (bop_list_product_left (bop_product mulA mulP) 
          (t ++ Yb ++ [(ah, bh + bh')]) s2) Z) (au, av) = true

        2.6 Simplify the goal
        set.in_set (manger_llex.eqAP A P eqA eqP)
        (fold_left (manger_merge_sets_new eqA addP)
        ltran_list_product (bop_product mulA mulP) (ah, bh + bh') s2 ++
        (bop_list_product_left (bop_product mulA mulP) 
          (t ++ Yb ) s2) Z) (au, av) = true

        2.7 Rewrite fold_left_app and we are home. 
    *)
    case_eq (set.in_set eqA (map fst Y) ah);
    intro He; swap 1 2.
    ++
      destruct (filter_not_in_set_no_dup Y ah He) as (Hel & Her).
      rewrite Hel in HeqYa;
      cbn in HeqYa.
      rewrite Her in HeqYb.
      rewrite HeqYa, HeqYb.
      rewrite ltr_bop_list_dist in Hd.
      remember (t ++ Y) as tY.
      rewrite app_assoc.
      rewrite <-HeqtY.
      eapply set_in_fold_left_swap_2; try assumption.
    ++
      assert (Hf : 
      (ltran_list_product (bop_product mulA mulP) (ah, bh) s2 ++
      bop_list_product_left (bop_product mulA mulP) (t ++ Y) s2) = 
      bop_list_product_left (bop_product mulA mulP) ([(ah, bh)] ++ t ++ Y) s2).
      cbn; reflexivity.
      rewrite Hf in Hd; clear Hf.
      (* split Y *)
      destruct (no_dup_split_list_aux Y ah Hb He) as 
      (bh' & Hf).
      destruct (nodup_inset_set Y ah bh' Hb Hf)
      as (Y₁ & Y₂ & Hg & Hi & Hj).
      pose proof in_set_subst_3 _ _ _ _ _ _ _ _ _ _ _ 
      Hc Hg Hd as Hdd; clear Hd.
      destruct (manger_merge_set_new_aux_congruence_left
      A P eqA eqP refA symA trnA refP symP trnP 
      Y (Y₁ ++ [(ah, bh')] ++ Y₂) ah Hg) as (Hkl & Hkr).
      rewrite <-HeqYb in Hkl.
      rewrite <-list_filter_lib_filter_same in Hkl.
      rewrite filter_app in Hkl; cbn in Hkl;
      rewrite refA in Hkl; cbn in Hkl;
      rewrite <-filter_app in Hkl;
      rewrite list_filter_lib_filter_same in Hkl.

      assert (Hn : brel_set (brel_product eqA eqP) Yb (Y₁ ++ Y₂) = true).
      eapply brel_set_transitive with 
      (t := (filter (λ '(s2, _), negb (eqA ah s2)) (Y₁ ++ Y₂)));
      [eapply refAP | eapply symAP | eapply trnAP | 
      exact Hkl |]; try assumption.
      eapply brel_set_not_member; try assumption.
      clear Hkl Hkr.
      assert (Hk : fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA ah s2) Y) (ah, bh) == 
      (ah, fold_left (λ t1 t2 : P, addP t1 t2) 
      (map snd (List.filter (λ '(x, _), eqA ah x) Y)) bh)).
      eapply fold_left_filter; try assumption.
      destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA ah s2) Y) (ah, bh)) as (x, y) eqn:Hl.
      eapply brel_product_elim in Hk.
      destruct Hk as [Hkl Hkr].
      rewrite list_filter_lib_filter_same in Hkr.
      assert (Hm : eqP y (addP bh bh') = true).
      eapply trnP with (fold_left (λ t1 t2 : P, addP t1 t2)
      (map snd (filter (λ '(x, _), eqA ah x) Y)) bh);
      [exact Hkr| ].
      eapply trnP with 
      (fold_left (λ t1 t2 : P, addP t1 t2)
      (map snd (filter (λ '(x0, _), eqA ah x0) [(ah, bh')])) bh).
      cbn; rewrite refA; cbn.
      (* Prove it separately. It's polluting the main proof *)
      eapply fold_left_map_filter_cong; try assumption.
      eapply brel_set_transitive with 
      (t := (filter (λ '(s0, _), eqA ah s0) (Y₁ ++ [(ah, bh')] ++ Y₂)));
      [eapply refAP | eapply symAP | eapply trnAP | |];
      try assumption.
      eapply filter_congruence_gen; try assumption.
      eapply  bop_congruecen_eqA.
      rewrite <-list_filter_lib_filter_same,
      filter_app; cbn;
      rewrite refA; cbn.
      repeat erewrite filter_arg_swap_gen with (a := ah);
      try assumption; try (eapply refA).
      repeat rewrite in_list_filter_empty; cbn; try assumption.
      eapply brel_set_reflexive;
      [eapply refAP | eapply symAP ];
      try assumption.
      cbn; rewrite refA; cbn;
      eapply refP.
      (* Now do the subsitution. *)
      rewrite HeqYa.
      eapply in_set_subst_4 with (ah := ah) (bh := bh) (bh' := bh');
      try assumption.
      exact Hn.
      pose proof in_set_swap_arugments_2 _ _ _ _ _ _ _ _ _ _ 
      Hc Hdd as Hddd; clear Hdd.
      rewrite app_assoc in Hddd |- *.
      rewrite app_assoc in Hddd |- *.
      remember ((t ++ Y₁) ++ Y₂) as tY.
      rewrite bop_list_product_left_app in Hddd |- *.
      rewrite fold_left_app in Hddd |- *.
      remember ((fold_left (manger_merge_sets_new eqA addP)
      (bop_list_product_left (bop_product mulA mulP) tY s2) Z)) as txyZ.
      eapply set_in_fold_dist_imp_2; try assumption.
      subst; eapply manger_merge_set_no_dup; 
      try assumption.
Qed.






Lemma bop_left_uop_inv_phase_1 : 
  bop_left_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_1 eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_1 eqA addP).
Proof.
    (* Think, Think, Think Mukesh *)
    (* 
      Calculation using Ha
      s1 := [(a, b); (c, d); (a, e)]
      s2 := [(u, v); (x, y); (x, t)]

    1. (uop_manger_phase_1 eqA addP s1) = 
      [(a, b + e); (c, d)]
      ---------------------------------------
    2. (manger_product_phase_0 eqA eqP mulA mulP
        [(a, b + e); (c, d)] [(u, v); (x, y); (x, t)]) = 
        -----------------------------------------------
        [(a * u, (b + e) * v); (a * x, (b + e) * y); 
        (a * x, (b + e) * t); (c * u, d * v); (c * x, d * y);
        (c * x, d * t)]
        ----------------------------------------------
    3. (uop_manger_phase_1 eqA addP  
        [(a * u, (b + e) * v); (a * x, (b + e) * y); 
        (a * x, (b + e) * t); (c * u, d * v); (c * x, d * y);
        (c * x, d * t)] = 
        ---------------------------------------------
        [(a * u, (b + e) * v); (a * x; (b + e) * y + (b + e) * t);
        (c * u, d * v); (c * x; d * y + d * t)]
        -----------------------------------------

    Calculation using the goal:
    5. (manger_product_phase_0 eqA eqP mulA mulP 
      [(a, b); (c, d); (a, e)] [(u, v); (x, y); (x, t)] = 
      -------------------------------------------------
      [(a * u, b * v); (a * x, b * y); (a * x, b * t);
      (c * u, d * v); (c * x, d * y); (c * x, d * t);
      (a * u, e * v); (a * x, e * y); (a * x, e * t)] 
    --------------------------------------------------
    6. uop_manger_phase_1 eqA addP 
        [(a * u, v * v); (a * x, b * y); (a * x, b * t);
        (c * u, d * v); (c * x, d * y); (c * x, d * t);
        (a * u, e * v); (a * x, e * y); (a * x, e * t)] = 
      -------------------------------------------------
      [(a * u, b * v + e * v); (a * x, b * y + b * t + e * y + e * t); 
        (c * u, d * d); (c * x, d * y + d * t)] 


    The problem with current intro and elim rule is that 
    we throw some information 
   

  This can be proven easily with commuativity and apply 
  bop_right_uop_inv_phase_1 and we are home.
  *)
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; try assumption.
  +
    unfold bop_reduce in Ha |- *.
    unfold uop_manger_phase_1,
    manger_phase_1_auxiliary in Ha |- *.
    rewrite manger_merge_set_funex in Ha |- *.
    (* How to generalise this? *)
    replace s1 with (s1 ++ []).
    eapply bop_left_uop_inv_phase_1_gen_forward;
    try reflexivity; try assumption.
    eapply app_nil_r.    
  +
    unfold bop_reduce in Ha |- *.
    unfold uop_manger_phase_1,
    manger_phase_1_auxiliary in Ha |- *.
    rewrite manger_merge_set_funex in Ha |- *.
    eapply  bop_left_uop_inv_phase_1_gen_backward;
    try reflexivity. 
    rewrite app_nil_r; try assumption.
Qed.



Lemma bop_left_uop_inv_phase_2 : 
  bop_left_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_2 lteA)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_2 lteA).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; try assumption.
  +
    unfold bop_reduce in Ha |- *.
Admitted.


(* generalise version  *)
(* Challenging, yet nice, proof. *)
Lemma bop_right_uop_inv_phase_1_gen_foward : 
  forall (s1 s2 Y Z : finite_set (A * P)) au av, 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP s1
        (fold_left (manger_merge_sets_new eqA addP) s2 Y)) Z) 
          (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP s1 (s2 ++ Y)) Z) 
        (au, av) = true.
Proof.
  (* Don't touch s2 *)
  (* Also, don't use fold_left *)
  refine (fix Fn s1 := 
    match s1 as s1' return s1 = s1' -> _ with 
    | [] => _ 
    | (ah, bh) :: t => _ 
    end eq_refl).
  +
    intros Ha * Hb Hc Hd.
    cbn in Hd |- *.
    exact Hd.
  +
    intros Ha * Hb Hc Hd;
    cbn in Hd |- *.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh) 
    (fold_left (manger_merge_sets_new eqA addP) s2 Y)) as Ya.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh) (s2 ++ Y)) 
    as Yb.
    (* 
      Now I invoke fold_left_manger_merge_set_idempotent 
    *)
    (* remove the set.uop_duplicate_elim from Hd and goal *)
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP)
      (Yb ++ bop_list_product_left (bop_product mulA mulP) t (s2 ++ Y)) Z);
      [| eapply symAP | eapply trnAP | 
      eapply fold_left_manger_merge_set_idempotent]; try assumption.
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP) 
      (Ya ++ bop_list_product_left (bop_product mulA mulP) t
      (fold_left (manger_merge_sets_new eqA addP) s2 Y)) Z) in Hd;
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.

    (* some unfold of definitions to apply induction hypothesis *)
    unfold manger_product_phase_0, bop_lift in Hd, Fn.
    rewrite fold_left_app in Hd |- *.
    specialize (Fn t s2 Y 
      (fold_left (manger_merge_sets_new eqA addP) Ya Z) au av Hb).
    
    (* prove that it's duplicate free *)
    assert (He : no_dup eqA (map fst (fold_left 
      (manger_merge_sets_new eqA addP) Ya Z)) = true). 
    subst. eapply manger_ltrtrans_duplicate_free_forward;
    try assumption.
    (* instantiate the IHn *)
    specialize (Fn He).
    (* remove uop_duplicate from Fn *)
    erewrite in_set_left_congruence_v2 with 
    (Y := (fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP) t
       (fold_left (manger_merge_sets_new eqA addP) s2 Y))
    (fold_left (manger_merge_sets_new eqA addP) Ya Z))) in Fn;
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    specialize (Fn Hd).
    rewrite in_set_left_congruence_v2 with 
    (Y := (fold_left (manger_merge_sets_new eqA addP)
       (bop_list_product_left (bop_product mulA mulP) t (s2 ++ Y))
      (fold_left (manger_merge_sets_new eqA addP) Ya Z))) in Fn;
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    (* Now one more challenge left*)
    subst. clear Hd He.
    remember ((fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (
       ah, bh) (fold_left (manger_merge_sets_new eqA addP) s2 Y))
    Z)) as Za.
    remember ((fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (ah, bh) (s2 ++ Y)) Z))
    as Zb.
    assert (Hd : Za =S= Zb).
    subst; eapply  fold_left_ltrtrans_interaction;
    try assumption.
    eapply fold_left_in_set_mmsn_cong with (V := Za); try assumption.
    exact addP_gen_idempotent.
Qed.
   
   


Lemma bop_right_uop_inv_phase_1_gen_backward : 
  forall (s1 s2 Y Z : finite_set (A * P)) au av, 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP s1 (s2 ++ Y)) Z) 
        (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP s1
        (fold_left (manger_merge_sets_new eqA addP) s2 Y)) Z) 
          (au, av) = true.
Proof.
  refine (fix Fn s1 := 
    match s1 as s1' return s1 = s1' -> _ with 
    | [] => _ 
    | (ah, bh) :: t => _ 
    end eq_refl).
  +
    intros * Ha * Hb Hc Hd.
    cbn in Hd |-*;
    exact Hd.
  +
    intros * Ha * Hb Hc Hd.
    cbn in Hd |- *.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh) 
    (fold_left (manger_merge_sets_new eqA addP) s2 Y)) as Ya.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh) (s2 ++ Y)) 
    as Yb.
    (* get rid of set.uop_duplicate_elim *)
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP) 
      (Ya ++ bop_list_product_left (bop_product mulA mulP) t
      (fold_left (manger_merge_sets_new eqA addP) s2 Y)) Z);
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.

    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP)
      (Yb ++ bop_list_product_left (bop_product mulA mulP) t (s2 ++ Y)) Z) 
    in Hd; [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    (* some unfold of definitions to apply induction hypothesis *)
    unfold manger_product_phase_0, bop_lift in Hd, Fn.
    rewrite fold_left_app in Hd |- *.
    specialize (Fn t s2 Y 
      (fold_left (manger_merge_sets_new eqA addP) Yb Z) au av Hb).
    (* prove that it's duplicate free *)
    assert (He : no_dup eqA (map fst (fold_left 
      (manger_merge_sets_new eqA addP) Yb Z)) = true). 
    subst. eapply manger_ltrtrans_duplicate_free_backward;
    try assumption.
    (* instantiate the IHn *)
    specialize (Fn He).
    rewrite in_set_left_congruence_v2 with 
    (Y := (fold_left (manger_merge_sets_new eqA addP)
       (bop_list_product_left (bop_product mulA mulP) t (s2 ++ Y))
      (fold_left (manger_merge_sets_new eqA addP) Yb Z))) in Fn;
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    specialize (Fn Hd).
    erewrite in_set_left_congruence_v2 with 
    (Y := (fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP) t
       (fold_left (manger_merge_sets_new eqA addP) s2 Y))
    (fold_left (manger_merge_sets_new eqA addP) Yb Z))) in Fn;
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    subst. clear Hd He.
    remember ((fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (
       ah, bh) (fold_left (manger_merge_sets_new eqA addP) s2 Y))
    Z)) as Za.
    remember ((fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (ah, bh) (s2 ++ Y)) Z))
    as Zb.
    (* 
      Now the challenge is to prove if this goal 
      is a reduction 
      If I can prove that Za and Zb are same, then we 
      are home. 
    *) 
    assert (Hd : Za =S= Zb).
    subst; eapply  fold_left_ltrtrans_interaction;
    try assumption.
    eapply fold_left_in_set_mmsn_cong with (V := Zb); try assumption.
    exact addP_gen_idempotent.
    eapply brel_set_symmetric.
    exact Hd.
Qed.



(* I need to generalise this to do induction. *)
Lemma bop_right_uop_inv_phase_1 : 
  bop_right_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_1 eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_1 eqA addP).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; 
  try assumption.
  +
    unfold bop_reduce in Ha |- *.
    unfold uop_manger_phase_1,
    manger_phase_1_auxiliary in Ha |- *.
    rewrite manger_merge_set_funex in Ha |- *.
    replace s2 with (s2 ++ []).
    eapply bop_right_uop_inv_phase_1_gen_foward;
    [try reflexivity | try reflexivity | exact Ha].
    eapply app_nil_r.
  +
    unfold bop_reduce in Ha |- *.
    unfold uop_manger_phase_1,
    manger_phase_1_auxiliary in Ha |- *.
    rewrite manger_merge_set_funex in Ha |- *.
    replace s2 with (s2 ++ []) in Ha.
    eapply bop_right_uop_inv_phase_1_gen_backward;
    [try reflexivity | try reflexivity | exact Ha].
    eapply app_nil_r.
Qed.



Lemma bop_right_uop_inv_phase_2 : 
  bop_right_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_2 lteA)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_2 lteA).
Proof. 
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; try assumption.
  +
    unfold bop_reduce, uop_manger_phase_2 in Ha |- *.
    

Admitted. 



(* This require mulA and mulP to be commutative  *)
Lemma manger_product_phase_0_commutative 
  (mulA_comm : bop_commutative A eqA mulA)
  (mulP_comm : bop_commutative P eqP mulP) : 
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
  

(* Proof starts from here *)


Lemma bop_left_uop_inv :
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (@uop_manger A P eqA lteA addP)
    (manger_product_phase_0 eqA eqP mulA mulP))
    (@uop_manger A P eqA lteA addP).
Proof.
  eapply composition_left_uop_invariant.
  + eapply symSAP.
  + eapply trnSAP; try assumption.
  + eapply P1_cong with (lteA := lteA) (zeroP := zeroP)
    (fA := fA); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with (fA := fA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
Qed.


(*
    The multiplicative component of the active part is 
    cancellative or multiplicative component of the 
    passive part is constant. 
    mulA is cancellative 
    Definition uop_manger := uop_compose [P2] [P1].
*)
Lemma bop_right_uop_inv :
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (@uop_manger A P eqA lteA addP)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (@uop_manger A P eqA lteA addP).
Proof.
  eapply composition_right_uop_invariant.
  + eapply symSAP.
  + eapply trnSAP; try assumption.
  + eapply P1_cong with (lteA := lteA) (zeroP := zeroP)
    (fA := fA); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with (fA := fA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
Qed.




Lemma bop_manger_product_congruence : 
  bop_congruence _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  apply uop_compose_bop_congruence.
  + eapply symSAP.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent). 
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with (fA := fA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
Qed.

(* mulA and mulP has to be associative *)
Lemma bop_manger_product_phase_0_assoc : 
  bop_associative (finite_set (A * P)) (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros X Y Z.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Ha];
  try assumption.
  + eapply lift_lemma_1;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_assoc | exact Ha];
    try assumption.
  + eapply lift_lemma_2;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_assoc | exact Ha];
    try assumption.
Qed.
  

Lemma bop_manger_product_associative : 
  bop_associative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  apply uop_compose_bop_associative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply bop_manger_product_phase_0_assoc.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent). 
  + eapply P1_idem;try assumption;
    try (eapply addP_gen_idempotent). 
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with (fA := fA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
Qed.



Lemma bop_manger_product_commutative 
  (mulA_comm : bop_commutative A eqA mulA)
  (mulP_comm : bop_commutative P eqP mulP) :
  bop_commutative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  eapply uop_compose_bop_commutative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent). 
  + eapply P1_idem;try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with (fA := fA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply manger_product_phase_0_commutative; 
    try assumption.
Qed.


End Theory.  

