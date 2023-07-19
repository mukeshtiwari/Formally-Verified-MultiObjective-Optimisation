Require Import Coq.Lists.List
  Psatz.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.theory.set. (* for in_set lemmas *) 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.trivial. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.or.
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product.
Require Import CAS.coq.algorithms.matrix_algorithms.
Require Import CAS.coq.uop.properties.
Require Import CAS.coq.po.theory.
Require Import CAS.coq.eqv.list.


Import ListNotations.

Section Computation.

(*
• Phase 1. All pairs from X with equal active components are merged
into a single pair whose active component is the one found in the
original pairs and passive component is the join of passive components
from the original pairs. For instance, if X contains altogether three
pairs with a given x ∈ P , i.e., (x, x1 ), (x, x2 ) and (x, x3 ), then they are
replaced with a single pair (x, x1 ∨ x2 ∨ x3 ). Note that after phase 1
all pairs in X have distinct active components.

• Phase 2. All pairs from X that are dominated in X with respect
to their active components are deleted from X. For instance, if X
contains two pairs (x, x') and (y, y') such that x ≺ y, then the pair
(x, x') is deleted. In other words, phase 2 leaves in X only those pairs
that are efficient according to their active component.

TGG22: Note that Manger's order is the dual of our left order. 
*)   

(* 
  A = type of active component
  P = type of passive component
*)   
Fixpoint manger_merge_sets
           {A P : Type}
           (eqA : brel A)
           (addP : binary_op P)
           (Y : finite_set (A * P))
           (p1 : A * P) :=
  match Y with
  | nil => p1 :: nil
  | p2 :: Y' =>
    match p1, p2 with
    | (s1, t1), (s2, t2) =>
      if eqA s1 s2
      then manger_merge_sets eqA addP Y' (s1, addP t1 t2) 
      else p2 :: (manger_merge_sets eqA addP Y' p1) 
    end 
  end.



(* 
This makes the current proof that I am trying is bit easier.
The manger_merge_sets and manger_merge_sets_new are 
equivalent.
*)


Definition manger_merge_sets_new_aux
  {A P : Type}
  (eqA : brel A)
  (addP : binary_op P)
  (Y : finite_set (A * P))
  (p1 : A * P) : list (A * P) * list (A * P) :=
    ((filter (λ '(s2, t2), eqA (fst p1) s2) Y),
    (filter (λ '(s2, t2), negb (eqA (fst p1) s2)) Y)).


Definition manger_merge_sets_new
  {A P : Type}
  (eqA : brel A)
  (addP : binary_op P)
  (Y : finite_set (A * P))
  (p1 : A * P) : list (A * P) :=
    match manger_merge_sets_new_aux eqA addP Y p1 with 
    | (Y1, Y2) => 
        Y2 ++ 
        [(fold_left 
          (λ '(s1, t1) '(s2, t2), (s1, addP t1 t2)) 
          Y1 p1)] 
    end.



Definition manger_phase_1_auxiliary 
          {A P : Type}
          (eqA : brel A)
          (addP : binary_op P) 
          (Y : finite_set (A * P))
          (X : finite_set (A * P))  : finite_set (A * P) :=
  fold_left (manger_merge_sets eqA addP) X Y.



Definition uop_manger_phase_1 
          {A P : Type}
          (eqA : brel A)
          (addP : binary_op P) 
          (X : finite_set (A * P))  : finite_set (A * P) :=
  manger_phase_1_auxiliary  eqA addP nil X.   

Definition equal_manger_phase_1 
          {A P : Type}
          (eqA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, brel_set (brel_product eqA eqP)
                  (uop_manger_phase_1 eqA addP X)
                  (uop_manger_phase_1 eqA addP Z). 

Definition manger_pre_order
           {A P : Type}
           (lteA : brel A) : brel (A * P)
  := brel_product lteA (@brel_trivial P). 

Definition uop_manger_phase_2
           {A P : Type} (lteA : brel A) : unary_op (finite_set (A * P))          
  := uop_minset (manger_pre_order lteA). 

Definition equal_manger_phase_2
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P) : brel (finite_set (A * P)) :=         
  λ X Z, brel_set (brel_product eqA eqP)
                  (uop_manger_phase_2 lteA X)
                  (uop_manger_phase_2 lteA Z). 

Definition equal_manger
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, equal_manger_phase_1 eqA eqP addP 
                  (@uop_manger_phase_2 A P lteA X)
                  (@uop_manger_phase_2 A P lteA Z).

Definition equal_manger_v2
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, @equal_manger_phase_2 A P eqA lteA eqP 
                  (uop_manger_phase_1 eqA addP X)
                  (uop_manger_phase_1 eqA addP Z).

(* conjecture these two equalities are the same *) 


End Computation. 

Section Theory.


Variables (A P : Type) 
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P)
          (zeroP : P)
          (* *)
          (zeropLid : ∀ (p : P), eqP (addP zeroP p) p = true)
          (zeropRid : ∀ (p : P), eqP (addP p zeroP) p = true)
          (refA : brel_reflexive A eqA)
          (symA : brel_symmetric A eqA)
          (trnA : brel_transitive A eqA)
          (refP : brel_reflexive P eqP)
          (symP : brel_symmetric P eqP)
          (trnP : brel_transitive P eqP)
          (cong_addP : bop_congruence P eqP addP) 
          (cong_lteA : brel_congruence A eqA lteA)
          (cong_eqP : brel_congruence P eqP eqP)
          (cong_eqA : brel_congruence A eqA eqA)
          (ref_lteA : brel_reflexive A lteA)
          (trn_lteA: brel_transitive A lteA)
          (* is idemP really needed, or is it 
             a consequence of using lists to represent sets?
          *) 
          (idemP : bop_idempotent P eqP addP)
          (* Extra assumptions needed to prove the lemmas fold_left congruence *)
          (addP_assoc : bop_associative P eqP addP)
          (addP_com : bop_commutative P eqP addP)
          (* idempotence is baked in this addP_gen_idempotent but it can be proved *)
          (addP_gen_idempotent : ∀ x y : P, eqP x y = true → eqP (addP x y) y = true).

      

Local Notation "a [in] X" := (in_set (brel_product eqA eqP) X a = true) (at level 70).
Local Notation "a == b"   := (brel_product eqA eqP a b = true) (at level 70).
Local Notation "a <A> b"  := (eqA a b = false) (at level 70). 

Local Notation "[MMS]"  := (manger_merge_sets eqA addP).
Local Notation "[P1AX]" := (manger_phase_1_auxiliary eqA addP).
Local Notation "[P1]"   := (uop_manger_phase_1 eqA addP).
Local Notation "[P2]"   := (uop_manger_phase_2 lteA).

Local Notation "[EQ]"    := (brel_set (brel_product eqA eqP)).
Local Notation "a =S= b" := (brel_set (brel_product eqA eqP) a b = true) (at level 70). 
Local Notation "[EQ1]"   := (equal_manger_phase_1 eqA eqP addP). 
Local Notation "[EQM]"   := (equal_manger eqA lteA eqP addP).


(* equality on A * P *) 
Lemma refAP : brel_reflexive (A * P) (brel_product eqA eqP).
Proof. apply brel_product_reflexive; auto. Qed. 

Lemma symAP : brel_symmetric (A * P) (brel_product eqA eqP).
Proof. apply brel_product_symmetric; auto. Qed. 

Lemma trnAP : brel_transitive (A * P) (brel_product eqA eqP).
Proof. apply brel_product_transitive; auto. Qed. 

(* equality on set over A * P *)

Lemma refSetAP : brel_reflexive _ [EQ]. 
Proof. apply brel_set_reflexive.
       - apply refAP.
       - apply symAP. 
Qed. 

Lemma symSetAP : brel_symmetric _ [EQ]. 
Proof. apply brel_set_symmetric. Qed. 

Lemma trnSetAP : brel_transitive _ [EQ]. 
Proof. apply brel_set_transitive.
       - apply refAP.
       - apply symAP.
       - apply trnAP. 
Qed. 

Lemma set_equal_with_cons_left :
  ∀ X p1 p2, p1 == p2 -> (p1 :: X) =S= (p2 :: X) . 
Proof. intros X p1 p2 H1.
       apply brel_set_intro_prop.
       - apply refAP.
       - split; intros a H2. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. apply symAP in H1.
                   exact (trnAP _ _ _ H1 H2). 
                ++ right. exact H2. 
             -- apply symAP. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. 
                   exact (trnAP _ _ _ H1 H2). 
                ++ right. exact H2. 
             -- apply symAP. 
Qed.

Lemma set_equal_with_cons_right :
  ∀ X Y p, X =S= Y -> (p :: X) =S= (p :: Y) . 
Proof. intros X Y p H1.
       apply brel_set_intro_prop.
       - apply refAP.
       - split; intros a H2. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. exact H2.
                ++ right.
                   rewrite (in_set_left_congruence _ _ symAP trnAP a _ _ H1) in H2.
                   exact H2. 
            -- apply symAP. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. exact H2.
                ++ right.
                   rewrite (in_set_left_congruence _ _ symAP trnAP a _ _ H1).
                   exact H2. 
             -- apply symAP. 
Qed.

Lemma remove_duplicate_from_set :
  ∀ Y p1 p2, p1 == p2 -> (p1 :: p2 :: Y) =S= (p1 :: Y).
Proof. intros Y p1 p2 H1.
       apply brel_set_intro_prop.
       - apply refAP. 
       - split; intros a H2. 
         + apply in_set_cons_intro.
           * apply symAP. 
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left; auto. 
                ++ apply in_set_cons_elim in H2.
                   ** destruct H2 as [H2 | H2].
                      --- left. exact (trnAP _ _ _ H1 H2). 
                      --- right; auto. 
                   ** apply symAP. 
             -- apply symAP. 
         + apply in_set_cons_intro.
           * apply symAP. 
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left; auto. 
                ++ right.
                   apply in_set_cons_intro; auto.
                   apply symAP. 
             -- apply symAP.
Qed. 
                
Lemma set_rearrange_v1 :
  ∀ Y p1 p2, (p1 :: p2 :: Y) =S= (p2:: p1 :: Y).
Proof. intros Y p1 p2.
       apply brel_set_intro_prop.
       - apply refAP. 
       - split; intros p3 H1.
         + (*
  H1 : p3 [in] p1 :: p2 :: Y
  ============================
  p3 [in] p2 :: p1 :: Y
            *)
           apply in_set_cons_intro.
           * apply symAP.
           * apply in_set_cons_elim in H1.
             -- destruct H1 as [H1 | H1].
                ++ right.
                   apply in_set_cons_intro.
                   ** apply symAP.
                   ** left. auto. 
                ++ apply in_set_cons_elim in H1.
                   --- destruct H1 as [H1 | H1].
                       +++ left. auto.
                       +++ right. 
                           apply in_set_cons_intro.
                           *** apply symAP.
                           *** right. auto.
                   --- apply symAP.
             -- apply symAP.
         + (* same code! 

  H1 : p3 [in] p2 :: p1 :: Y
  ============================
  p3 [in] p1 :: p2 :: Y
           *)
           apply in_set_cons_intro.
           * apply symAP.
           * apply in_set_cons_elim in H1.
             -- destruct H1 as [H1 | H1].
                ++ right.
                   apply in_set_cons_intro.
                   ** apply symAP.
                   ** left. auto. 
                ++ apply in_set_cons_elim in H1.
                   --- destruct H1 as [H1 | H1].
                       +++ left. auto.
                       +++ right. 
                           apply in_set_cons_intro.
                           *** apply symAP.
                           *** right. auto.
                   --- apply symAP.
             -- apply symAP.
Qed.

Lemma set_rearrange_v2 : 
   ∀ X Y p,  p :: X ++ Y =S= X ++ p :: Y.
Proof. induction X; intros Y p. 
       - rewrite app_nil_l. rewrite app_nil_l.
         apply refSetAP. 
       - rewrite <- app_comm_cons. rewrite <- app_comm_cons. 
         assert (H1 := set_rearrange_v1 (X ++ Y) p a).
         assert (H2 := IHX Y p). 
         assert (H3 := set_equal_with_cons_right (p :: X ++ Y) (X ++ p :: Y) a H2). 
         exact (trnSetAP _ _ _ H1 H3).
Qed. 
                   
(* properties of manger_pre_order *)  

Lemma manger_pre_order_congruence : brel_congruence (A * P) (brel_product eqA eqP) (manger_pre_order lteA). 
Proof. unfold manger_pre_order.
       apply brel_product_congruence; auto.
       apply brel_trivial_congruence. 
Qed.

Lemma manger_pre_order_reflexive : brel_reflexive (A * P) (manger_pre_order lteA).
Proof. unfold manger_pre_order.
       apply brel_product_reflexive; auto.
       apply brel_trivial_reflexive. 
Qed.

 
Lemma manger_pre_order_transitive :
  brel_transitive (A * P) (manger_pre_order lteA).
Proof.
  apply brel_product_transitive;
  auto.
  eapply brel_trivial_transitive.
Qed.


(* properties of equality [EQ1] *)

Lemma equal_manger_phase_1_congruence : brel_congruence _ [EQ1] [EQ1].
Proof. intros X Y Z W. unfold equal_manger_phase_1.
       apply brel_set_congruence.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
Qed.

Lemma equal_manger_phase_1_reflexive : brel_reflexive _ [EQ1].
Proof. intro X. unfold equal_manger_phase_1. 
       apply brel_set_reflexive; auto. 
       + apply refAP. 
       + apply symAP. 
Qed. 

Lemma equal_manger_phase_1_symmetric : brel_symmetric _ [EQ1].
Proof. unfold equal_manger_phase_1. intros X Y. 
       apply brel_set_symmetric; auto.
Qed. 

Lemma equal_manger_phase_1_transitive : brel_transitive _ [EQ1].
Proof. unfold equal_manger_phase_1. intros X Y Z. 
       apply brel_set_transitive; auto.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
Qed. 

(* properties of equality [EQM] *)

Lemma equal_manger_congruence : brel_congruence _ [EQM] [EQM].
Proof. intros X Y Z W. unfold equal_manger. 
       apply equal_manger_phase_1_congruence.
Qed.

Lemma equal_manger_reflexive : brel_reflexive _ [EQM].
Proof. unfold equal_manger; intro X; 
       apply equal_manger_phase_1_reflexive.
Qed.        

Lemma equal_manger_symmetric : brel_symmetric _ [EQM].
Proof. unfold equal_manger; intros X Y; 
       apply equal_manger_phase_1_symmetric.
Qed.        


Lemma equal_manger_transitive : brel_transitive _ [EQM].
Proof. unfold equal_manger; intros X Y Z; 
       apply equal_manger_phase_1_transitive.
Qed.        

(* Idempotence of reductions *)

Definition fst_unique_in_set X :=
  ∀ a a' p p',  (a, p) [in] X ->  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a').

Lemma singleton_uniqueness : ∀ p, fst_unique_in_set (p :: nil). 
Proof. destruct p as [a p].
       intros a1 a2 p1 p2 H2 H3. left.
       apply in_set_singleton_elim in H2, H3; try (apply symAP).
       apply symAP in H3.
       exact(trnAP _ _ _ H3 H2). 
Qed.

Lemma fst_unique_in_set_congruence :
  ∀ X Y, X =S= Y -> fst_unique_in_set X -> fst_unique_in_set Y.
Proof. unfold fst_unique_in_set.
       intros X Y H1 H2 a a' p p' H3 H4.
       assert (H5 : (a, p) [in] X).
       {
         rewrite (in_set_left_congruence _ _ symAP trnAP (a,p) _ _ H1).
         exact H3. 
       } 
       assert (H6 : (a', p') [in] X).
       {
         rewrite (in_set_left_congruence _ _ symAP trnAP (a',p') _ _ H1).
         exact H4. 
       } 
       exact (H2 _ _ _ _ H5 H6). 
Qed. 


Lemma fst_unique_in_set_cons_intro : 
  ∀ X a p, (∀ a' p',  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a')) 
           -> (fst_unique_in_set X)
           -> fst_unique_in_set ((a,p) :: X). 
Proof. intros X a p H1 H2. unfold fst_unique_in_set.
       intros a' a'' p' p'' H3 H4.
       apply in_set_cons_elim in H3.
       - apply in_set_cons_elim in H4.
         + destruct H3 as [H3 | H3];
           destruct H4 as [H4 | H4].
           * left. apply symAP in H3.
             exact (trnAP _ _ _ H3 H4).
           * destruct (H1 _ _ H4) as [H5 | H5].
             -- left. apply symAP in H3.
                exact (trnAP _ _ _ H3 H5).
             -- right.
                apply brel_product_elim in H3.
                destruct H3 as [H3 _].
                case_eq(eqA a' a''); intro H6; auto.
                rewrite (trnA _ _ _ H3 H6) in H5.
                discriminate H5. 
           * destruct (H1 _ _ H3) as [H5 | H5].
             -- left. apply symAP in H5.
                exact (trnAP _ _ _ H5 H4).
             -- right.
                apply brel_product_elim in H4.
                destruct H4 as [H4 _].
                case_eq(eqA a' a''); intro H6; auto.
                apply symA in H6. rewrite (trnA _ _ _ H4 H6) in H5.
                discriminate H5. 
           * destruct (H1 _ _ H3) as [H5 | H5];
             destruct (H1 _ _ H4) as [H6 | H6].
             -- left. apply symAP in H5.
                exact (trnAP _ _ _ H5 H6).
             -- right.
                apply brel_product_elim in H5.
                destruct H5 as [H5 _].
                case_eq(eqA a' a''); intro H7; auto.
                rewrite (trnA _ _ _ H5 H7) in H6.
                discriminate H6.
             -- right.
                apply brel_product_elim in H6.
                destruct H6 as [H6 _].
                case_eq(eqA a' a''); intro H7; auto.
                apply symA in H7. rewrite (trnA _ _ _ H6 H7) in H5.
                discriminate H5.
             -- case_eq(eqA a' a''); intro H7.
                ++ left.
                   destruct (H2 _ _ _ _ H3 H4) as [H8 | H8].
                   ** exact H8. 
                   ** rewrite H7 in H8. discriminate H8.
                ++ right. reflexivity. 
         + apply symAP. 
       - apply symAP. 
Qed.

Lemma fst_unique_in_set_cons_elim : 
  ∀ X a p, fst_unique_in_set ((a,p) :: X) ->
           (∀ a' p',  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a')) 
           * 
           (fst_unique_in_set X).
Proof. intros X a p H1. split. 
       - intros a' p' H2.
         unfold fst_unique_in_set in H1.
         assert (H3 : (a, p) [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
           + left. apply refAP. 
         } 
         assert (H4 : (a', p') [in] (a, p) :: X). 
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         exact (H1 _ _ _ _ H3 H4). 
       - unfold fst_unique_in_set in *.
         intros a' a'' p' p'' H2 H3.
         assert (H4 : (a', p') [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         assert (H5 : (a'', p'') [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         exact (H1 _ _ _ _ H4 H5).          
Qed.

Lemma fst_unique_in_set_concat_elim_right :
  ∀ X Y, fst_unique_in_set (X ++ Y) -> fst_unique_in_set Y.
Proof. induction X; intros Y H1.
       - rewrite app_nil_l in H1. exact H1.
       - rewrite <- app_comm_cons in H1.
         destruct a as [a p]. 
         apply fst_unique_in_set_cons_elim in H1.
         destruct H1 as [_ H1].
         apply IHX; auto. 
Qed.                           

Lemma manger_merge_sets_unchanged : 
  ∀ Y a b p p',
    Y <> nil -> 
    a <A> b ->  (b, p') [in] ([MMS] Y (a, p)) -> (b, p') [in] Y. 
Proof. induction Y; intros s t p p' H0 H1 H2.
       - congruence. 
       - simpl in H2.
         destruct a as [a1 p1].
         case_eq(eqA s a1); intro H3; rewrite H3 in H2.
         + apply in_set_cons_intro.
           * apply symAP.
           * right. destruct Y.
             -- simpl in H2.
                apply bop_or_elim in H2.
                destruct H2 as [H2 | H2].
                ++ apply bop_and_elim in H2.
                   destruct H2 as [H2 H4].
                   apply symA in H2. rewrite H2 in H1.
                   discriminate H1.
                ++ discriminate H2. 
             -- assert (H4 : p0 :: Y ≠ nil). congruence.
                exact(IHY _ _ _ _ H4 H1 H2). 
         + apply in_set_cons_intro. 
           * apply symAP. 
           * destruct Y.
             -- simpl in H2.
                apply bop_or_elim in H2.
                destruct H2 as [H2 | H2].
                ** left. apply bop_and_elim in H2.
                   destruct H2 as [H2 H4]. 
                   apply brel_product_intro; auto. 
                ** apply bop_or_elim in H2.
                   destruct H2 as [H2 | H2].
                   --- apply bop_and_elim in H2.
                       destruct H2 as [H2 H4].
                       apply symA in H2. rewrite H2 in H1.
                       discriminate H1.
                   --- discriminate H2. 
             -- apply in_set_cons_elim in H2.
                ++ destruct H2 as [H2 | H2].
                   ** left. exact H2.
                   ** right.
                      assert (H4 : p0 :: Y ≠ nil). congruence. 
                      exact (IHY _ _ _ _ H4 H1 H2).
                ++ apply symAP. 
Qed. 



Lemma manger_merge_sets_unchanged_v2 : 
  ∀ Y a b p p',
    Y <> nil -> 
    a <A> b -> (b, p') [in] Y -> (b, p') [in] ([MMS] Y (a, p)).
Proof. induction Y; intros a1 a2 p1 p2 H0 H1 H2.
       - congruence. 
       - destruct a as [a3 p3].
         simpl. 
         apply in_set_cons_elim in H2.
         + destruct H2 as [H2 | H2]; 
             case_eq(eqA a1 a3); intro H3.
           * apply brel_product_elim in H2.
             destruct H2 as [H2 H4].
             rewrite (trnA _ _ _ H3 H2) in H1.
             discriminate H1. 
           * apply in_set_cons_intro.
             -- apply symAP.
             -- left. exact H2. 
           * destruct Y. 
             -- compute in H2. discriminate H2.
             -- assert (H4 : p :: Y ≠ nil). congruence.  
                exact(IHY _ _ (addP p1 p3) _ H4 H1 H2).
           * destruct Y. 
             -- compute in H2. discriminate H2.
             -- assert (H4 : p :: Y ≠ nil). congruence.  
                assert (H5 := IHY _ _ p1 _ H4 H1 H2).
                apply in_set_cons_intro.
                ++ apply symAP.
                ++ right. auto. 
         + apply symAP. 
Qed. 

Lemma manger_merge_sets_preserves_uniqueness : 
∀ Y p, fst_unique_in_set Y -> fst_unique_in_set ([MMS] Y p). 
Proof. induction Y; intros p H1. 
       - simpl. apply singleton_uniqueness.
       - destruct a as [a1 p1]. destruct p as [a2 p2].
         apply fst_unique_in_set_cons_elim in H1.
         destruct H1 as [H1 H2]. simpl.
         case_eq(eqA a2 a1); intro H3.
         + apply IHY. exact H2. 
         + apply fst_unique_in_set_cons_intro.
           * intros a' p' H4.
             case_eq(eqA a1 a'); intro H5.
             -- left. apply brel_product_intro; auto.
                assert (H6' : (a', p') == (a1, p')).
                {
                  apply brel_product_intro; auto. 
                } 
                assert (H6 : (a1, p') [in] [MMS] Y (a2, p2)).
                {
                  exact (in_set_right_congruence _ _ symAP trnAP _ _ _ H6' H4).
                }
                destruct Y.
                ++ simpl in H6. apply bop_or_elim in H6.
                   destruct H6 as [H6 | H6]. 
                   ** apply bop_and_elim in H6.
                      destruct H6 as [H6 H7].
                      apply symA in H6. rewrite H6 in H3.
                      discriminate H3.
                   **  discriminate H6.
                ++ assert (H99 : p :: Y <> nil). congruence. 
                   assert (H6'' := manger_merge_sets_unchanged _ _ _ _ _ H99 H3 H6). 
                   destruct (H1 _ _ H6'') as [H7 | H7].
                   ** apply brel_product_elim in H7; auto.
                      destruct H7 as [_ H7]. exact H7. 
                   ** rewrite refA in H7. discriminate H7.
             -- right. reflexivity. 
           * apply IHY; auto.
Qed. 


Lemma uop_manger_phase_1_auxiliary_preserves_uniqueness : 
    ∀ X Y, fst_unique_in_set Y -> fst_unique_in_set ([P1AX] Y X). 
Proof. induction X; intros Y H1.
       - simpl. exact H1. 
       - simpl. apply IHX.
         apply manger_merge_sets_preserves_uniqueness; auto. 
Qed. 

Lemma manger_merge_set_congruence_right :
  ∀ Y p1 p2, p1 == p2 -> ([MMS] Y p1) =S= ([MMS] Y p2). 
Proof. induction Y; intros [a1 p1] [a2 p2] H1.
       - simpl.
         apply set_equal_with_cons_left; auto. 
       - apply brel_product_elim in H1. 
         destruct H1 as [H1 H2]. 
         destruct a as [a3 p3]. simpl.
         case_eq(eqA a1 a3); intro H3; case_eq(eqA a2 a3); intro H4.
         + assert (H5 : (a1, addP p1 p3) == (a2, addP p2 p3)).
           {
             apply brel_product_intro; auto.
           }
           exact (IHY _ _ H5). 
         + apply symA in H1.
           rewrite (trnA _ _ _ H1 H3) in H4.
           discriminate H4. 
         + rewrite (trnA _ _ _ H1 H4) in H3.
           discriminate H3. 
         + assert (H5 : (a1, p1) == (a2, p2)).
           {
             apply brel_product_intro; auto.
           }
           assert (H6 := IHY _ _ H5).
           exact (set_equal_with_cons_right _ _ (a3, p3) H6). 
Qed.




Lemma filter_negb : 
  forall (X : list (A * P))
  (f : A -> bool),
  List.filter (λ '(s2, _), negb (f s2)) X ++ 
  List.filter (λ '(s2, _), f s2) X =S= X.
Proof.
  induction X as [|(ax, bx) X Ihx];
  intros f; cbn.
  + reflexivity.
  + case_eq (f ax); intros Ha;
    simpl.
    ++
      remember (List.filter (λ '(s2, _), 
        negb (f s2)) X) as Xt.
      remember (List.filter (λ '(s2, _), 
        f s2) X) as Yt.
      apply symSetAP.
      eapply trnSetAP.
      instantiate (1 := (ax, bx) :: Xt ++ Yt).
      +++
        apply set_equal_with_cons_right,
        symSetAP; subst; apply Ihx.
      +++
        apply set_rearrange_v2.
    ++
      apply set_equal_with_cons_right,
      Ihx.
Qed.



Lemma filter_congruence_gen : 
  forall X Y f,
  (theory.bProp_congruence _ 
    (brel_product eqA eqP) f) ->
  X =S= Y ->
  filter f X =S=
  filter f Y.
Proof.
  intros ? ? ? Fcong Ha.
  apply brel_set_intro_prop.
  + apply refAP.
  + split.
    ++
      intros (a, p) Hb.
      eapply in_set_filter_elim in Hb.
      destruct Hb as [Hbl Hbr].
      eapply in_set_filter_intro;
      [apply symAP | apply Fcong | 
        split; [exact Hbl | ]].
      apply brel_set_elim_prop in Ha.
      destruct Ha as [Hal Har].
      apply Hal, Hbr.
      apply symAP.
      apply trnAP.
      apply Fcong.
    ++ 
      intros (a, p) Hb.
      eapply in_set_filter_elim in Hb.
      destruct Hb as [Hbl Hbr].
      eapply in_set_filter_intro;
      [apply symAP | apply Fcong | 
        split; [exact Hbl | ]].
      apply brel_set_elim_prop in Ha.
      destruct Ha as [Hal Har].
      apply Har, Hbr.
      apply symAP.
      apply trnAP.
      apply Fcong.
  Qed. 

Lemma negb_eqP_congruence : 
  forall a : P,
  theory.bProp_congruence P 
    eqP (λ x : P, negb (eqP a x)).
Proof.
  intros ? x y Hx.
  f_equal.
  case_eq (eqP a x);
  case_eq (eqP a y);
  intros Ha Hb;
  try reflexivity.
  rewrite (trnP _ _ _ Hb Hx) in Ha;
  congruence.
  apply symP in Hx.
  rewrite (trnP _ _ _ Ha Hx) in Hb;
  congruence.
Qed.


Lemma bop_neg_bProp_product_cong : 
  forall (ax : A) (bx : P),
  theory.bProp_congruence (A * P) (brel_product eqA eqP)
  (λ p : A * P, negb (brel_product eqA eqP p (ax, bx))).
Proof.
  intros ax bx (ap, aq) (bp, bq) Ha.
  apply f_equal.
  apply brel_product_elim in Ha.
  destruct Ha as [Hal Har].
  eapply brel_product_congruence with 
    (rS := eqA) (rT := eqP).
  eapply cong_eqA.
  eapply cong_eqP.
  apply brel_product_intro;
  [exact Hal | exact Har].
  apply brel_product_intro;
  [apply refA | apply refP].
Qed.


Lemma bop_theory_bProp_congruence_negb : 
  forall (pa : A), 
  theory.bProp_congruence _ 
    (brel_product eqA eqP)
    (λ '(s2, _), negb (eqA pa s2)).
Proof.
  intros ?.
  unfold theory.bProp_congruence.
  intros (aa, ap) (ba, bp) He.
  f_equal.
  apply brel_product_elim in He.
  destruct He as [Hel Her].
  case_eq (eqA pa aa); intro Hf.
  rewrite (trnA pa aa ba Hf Hel);
  reflexivity.
  case_eq (eqA pa ba); intro Hg.
  apply symA in Hel.
  rewrite (trnA pa ba aa Hg Hel) in Hf;
  congruence.
  reflexivity.
Qed.

Lemma bop_congruence_bProp_eqA : 
  forall (pa : A),
  theory.bProp_congruence _ 
        (brel_product eqA eqP)
        (λ '(s2, _), eqA pa s2).
Proof.
  intros pa.
  unfold theory.bProp_congruence.
  intros (aa, ap) (ba, bp) He.
  apply brel_product_elim in He.
  destruct He as [Hel Her].
  case_eq (eqA pa aa); intro Hf.
  rewrite (trnA pa aa ba Hf Hel);
  reflexivity.
  case_eq (eqA pa ba); intro Hg.
  apply symA in Hel.
  rewrite (trnA pa ba aa Hg Hel) in Hf;
  congruence.
  reflexivity.
Qed.

Lemma manger_merge_set_new_aux_congruence_left :
  ∀ X Y pa, 
  X =S= Y -> 
  (filter (λ '(s2, _), negb (eqA pa s2)) X =S= 
    filter (λ '(s2, _), negb (eqA pa s2)) Y) ∧
  (filter (λ '(s2, _), eqA pa s2) X =S= 
    filter (λ '(s2, _), eqA pa s2) Y).
Proof.
  intros ? ? ? Ha.
  pose proof (filter_negb X (fun x => negb (eqA pa x))) as Hb.
  pose proof (filter_negb Y (eqA pa)) as Hc.
  apply symSetAP in Hc.
  pose proof (trnSetAP _ _ _ Ha Hc) as Hd.
  split.
  + assert (He : theory.bProp_congruence _ 
      (brel_product eqA eqP)
      (λ '(s2, _), negb (eqA pa s2))).
    eapply bop_theory_bProp_congruence_negb.
    eapply filter_congruence_gen;
    [exact He | exact Ha].
  + assert (He : theory.bProp_congruence _ 
      (brel_product eqA eqP)
      (λ '(s2, _), eqA pa s2)).
    eapply bop_congruence_bProp_eqA.
    eapply filter_congruence_gen;
    [exact He | exact Ha].
Qed.
  

(* 
If a ∈ X then by idempotence 
  a + (fold_right f p X) = (fold_right f p X). 
*)
Lemma fold_right_idempotent_aux_one : 
  forall (X : list P) (a p : P)
  (f : P -> P -> P),
  (forall x y z : P, 
    eqP (f x (f y z)) (f (f x y) z) = true) ->
  (forall x y : P, eqP (f x y) (f y x) = true) ->
  (forall (x y w v : P),
    eqP x y = true ->
    eqP w v = true ->
    eqP (f x w) (f y v) = true) ->
  (forall x y : P, eqP x y = true ->
    eqP (f x y) y = true) ->
  in_set eqP X a = true ->
  eqP (f a (fold_right f p X)) (fold_right f p X) = true.
Proof.
  induction X as [|x X IHx].
  + 
    intros ? ? ? fassoc fcom fcong Ha Hb.
    simpl in Hb;
    congruence.
  +
    intros ? ? ? fassoc fcom fcong Ha Hb.
    simpl in * |- *.
    case_eq ((in_set eqP X a));
    case_eq (eqP a x); 
    intros Hc Hd.
    ++ (* a = x *)
      remember ((fold_right f p X)) as w.
      (* I need f to be associative *)
      eapply trnP.
      eapply fassoc.
      eapply fcong. 
      eapply Ha.
      exact Hc.
      apply refP.
    ++
      (* Induction case *)
      pose proof IHx a p f fassoc fcom fcong Ha Hd as He.
      remember ((fold_right f p X)) as w.
      eapply trnP with (f a (f w x)).
      eapply fcong.
      eapply refP.
      eapply fcom.
      eapply trnP with (f (f a w) x).
      eapply fassoc.
      eapply trnP with (f w x).
      eapply fcong.
      exact He.
      apply refP.
      eapply fcom.
    ++
      remember ((fold_right f p X)) as w.
      (* I need f to be associative *)
      eapply trnP.
      eapply fassoc.
      eapply fcong. 
      eapply Ha.
      exact Hc.
      eapply refP.
    ++
      rewrite Hc, Hd in Hb;
      simpl in Hb; congruence.
Qed.



Lemma in_set_false : 
  forall (Y : list P) (a : P),
  in_set eqP (filter (λ x : P, negb (eqP a x)) Y) a = false.
Proof.
  induction Y as [|b Y IHy];
  simpl.
  + intros ?; reflexivity.
  + intros ?.
    case_eq (eqP a b); simpl; intro Ha.
    ++
      now rewrite IHy.
    ++
      now rewrite Ha, IHy.
Qed.





Lemma in_set_true_false : 
  forall (Y : list P) (a b : P),
  eqP b a = false ->
  in_set eqP Y a = true ->
  in_set eqP (filter (λ x : P, negb (eqP a x)) Y) b = true ->
  in_set eqP Y b = true.
Proof.
  induction Y as [|u Y IHy]; simpl.
  + 
    intros ? ? Ha Hb Hc.
    simpl in Hb;
    congruence.
  +
    intros ? ? Ha Hb Hc.
    case_eq (eqP a u);
    case_eq (in_set eqP Y a);
    intros Hd He.
    rewrite He in Hc;
    simpl in Hc.
    eapply bop_or_intro.
    right.
    eapply in_set_filter_elim in Hc.
    firstorder.
    intros x y Hx.
    apply negb_eqP_congruence;
    exact Hx.
    eapply bop_or_intro.
    rewrite He in Hc;
    simpl in Hc.
    eapply in_set_filter_elim in Hc.
    right; firstorder.
    eapply negb_eqP_congruence.
    rewrite He in Hc;
    simpl in Hc.
    eapply bop_or_elim in Hc.
    eapply bop_or_intro.
    destruct Hc as [Hc | Hc].
    left; auto.
    right. 
    eapply in_set_filter_elim in Hc.
    destruct Hc as [Hcl Hcr];
    auto.
    eapply negb_eqP_congruence.
    rewrite Hd, He in Hb;
    simpl in Hb; 
    congruence.
Qed.


Lemma in_set_not_member :
  forall (X : list P) (a b : P),
  in_set eqP X a = false ->
  in_set eqP X b = true ->
  eqP a b = false.
Proof.
  induction X as [|u X IHx];
  simpl.
  + congruence.
  + intros ? ? Ha Hb.
    eapply bop_or_elim in Hb.
    eapply bop_or_false_elim in Ha.
    destruct Ha as [Hal Har].
    destruct Hb as [Hb | Hb].
    case_eq (eqP a b);
    intro Hc.
    rewrite (trnP _ _ _ Hc Hb) in Hal;
    congruence.
    reflexivity.
    eapply IHx;
    try assumption.
Qed.



Lemma brel_set_filter : 
  forall (X Y : list P) (a : P),
  in_set eqP X a = false ->
  brel_set eqP (a :: X) Y = true ->
  brel_set eqP X (filter (λ x : P, negb (eqP a x)) Y) = true.
Proof.
  intros ? ? ? Ha Hb.
  eapply brel_set_elim_prop in Hb;
  try assumption.
  destruct Hb as [Hbl Hbr].
  eapply brel_set_intro_prop;
  try assumption.
  split.
  +
    intros ? Hb.
    eapply in_set_filter_intro;
    try assumption.
    eapply negb_eqP_congruence.
    split.
    eapply Bool.negb_true_iff.
    eapply in_set_not_member;
    [exact Ha | exact Hb].
    eapply Hbl.
    eapply in_set_cons_intro;
    try assumption.
    right.
    exact Hb.
  +
    intros ? Hb.
    eapply in_set_filter_elim in Hb.
    destruct Hb as [Hba Hbb].
    pose proof Hbr a0 Hbb as Hc.
    eapply in_set_cons_elim in Hc;
    try assumption.
    eapply Bool.negb_true_iff in Hba.
    destruct Hc as [Hc | Hc].
    rewrite Hba in Hc.
    congruence.
    exact Hc.
    eapply negb_eqP_congruence.
Qed.


Lemma fold_right_in_set_false :
  forall (X : list P) (a p : P)
  (f : P -> P -> P),
  (forall (x y w v : P),
    eqP x y = true ->
    eqP w v = true ->
    eqP (f x w) (f y v) = true) ->
  in_set eqP X a = false ->
  eqP 
    (fold_right f p X)
    (fold_right f p 
      (filter (λ x : P, negb (eqP a x)) X)) = true.
Proof.
  induction X as [|ax X IHx];
  simpl.
  + 
    intros ? ? ? fcong Hb.
    apply refP.
  +
    intros ? ? ? fcong Hb.
    case_eq (in_set eqP X a);
    case_eq (eqP a ax);
    intros Hc Hd.
    ++
      rewrite Hc, Hd in Hb; 
      simpl in Hb;
      congruence.
    ++
      rewrite Hc, Hd in Hb; 
      simpl in Hb;
      congruence.
    ++
      rewrite Hc, Hd in Hb; 
      simpl in Hb;
      congruence.
    ++
      simpl.
      eapply fcong.
      eapply refP.
      eapply IHx;
      try assumption.
Qed.


Lemma fold_right_in_set :
  forall (X : list P) (a p : P)
  (f : P -> P -> P),
  (forall x y z : P, 
    eqP (f x (f y z)) (f (f x y) z) = true) ->
  (forall x y : P, eqP (f x y) (f y x) = true) ->
  (forall (x y w v : P),
    eqP x y = true ->
    eqP w v = true ->
    eqP (f x w) (f y v) = true) ->
  (forall x y : P, eqP x y = true ->
    eqP (f x y) y = true) ->
  in_set eqP X a = true ->
  eqP (fold_right f p X) 
    (f a (fold_right f p 
      (filter (fun x => negb (eqP a x)) X))) = true.
Proof.
  induction X as [|ax X IHx];
  simpl.
  + 
    intros ? ? ? fassoc fcom fcong Ha Hb.
    simpl in Hb;
    congruence.
  +
    intros ? ? ? fassoc fcom fcong Ha Hb.
    simpl in * |- *.
    case_eq ((in_set eqP X a));
    case_eq (eqP a ax); 
    intros Hc Hd;
    simpl.
    ++ (* a = x *)
      pose proof IHx a p f fassoc fcom
        fcong Ha Hd as He.
      remember (fold_right f p X) as w.
      remember (fold_right f p 
        (filter (λ x : P, negb (eqP a x)) X)) as v.
      eapply trnP with (f ax (f a v)).
      eapply fcong.
      eapply refP.
      exact He.
      assert (Ht : eqP (f ax (f a v)) 
        (f (f ax a) v) = true).
      eapply fassoc.
      rewrite <-Ht.
      eapply cong_eqP.
      eapply refP.
      eapply fcong.
      eapply symP.
      eapply Ha.
      eapply symP.
      exact Hc.
      eapply refP.
    ++ 
      (* Induction case *)
      pose proof IHx a p f fassoc fcom fcong
        Ha Hd as He.
      remember (fold_right f p X) as w.
      remember (fold_right f p 
        (filter (λ x : P, negb (eqP a x)) X)) as v.
      eapply trnP with (f ax (f a v)).
      eapply fcong.
      eapply refP.
      exact He.
      eapply trnP with (f (f ax a) v).
      eapply fassoc.
      eapply trnP with (f (f a ax) v).
      eapply fcong.
      eapply fcom.
      eapply refP.
      eapply symP.
      eapply fassoc.
    ++
      remember (fold_right f p X) as w.
      remember (fold_right f p 
        (filter (λ x : P, negb (eqP a x)) X)) as v.
      apply fcong.
      eapply symP;
      exact Hc.
      subst.
      eapply fold_right_in_set_false;
      try assumption.
    ++
      rewrite Hc, Hd in Hb;
      simpl in Hb; congruence.
Qed.



Lemma fold_right_congruence : 
  forall (X Y : list P) (p : P)
  (f : P -> P -> P),
  (forall x y z : P, 
    eqP (f x (f y z)) (f (f x y) z) = true) ->
  (forall x y : P, eqP (f x y) (f y x) = true) ->
  (forall (x y w v : P),
    eqP x y = true ->
    eqP w v = true ->
    eqP (f x w) (f y v) = true) ->
  (forall x y : P, eqP x y = true ->
    eqP (f x y) y = true) ->
  brel_set eqP X Y = true ->
  eqP (fold_right f p X) (fold_right f p Y) = true.
Proof.
  induction X as [|a X IHx].
  + 
    intros ? ? ? ? fassoc fcom fcong Ha.
    eapply brel_set_nil in Ha;
    rewrite Ha;
    simpl;
    apply refP.
  + (* Inducation Case *)
    simpl;
    intros ? ? ? fassoc fcom fcong Ha Hb.
    destruct (in_set eqP X a) eqn:Hc.
    ++
      assert (Hd : brel_set eqP X Y = true).
      apply brel_set_elim_prop in Hb;
      [|apply symP | apply trnP].
      destruct Hb as [Hbl Hbr].
      eapply brel_set_intro_prop.
      apply refP.
      split.
      +++
        intros ? Hd.
        eapply Hbl.
        eapply in_set_cons_intro.
        apply symP.
        right.
        exact Hd.
      +++
        intros ? Hd.
        pose proof (Hbr _ Hd) as He.
        apply in_set_cons_elim in He.
        destruct He as [He | He].
        eapply in_set_right_congruence.
        apply symP.
        apply trnP.
        exact He.
        exact Hc.
        exact He.
        apply symP.
      +++
        eapply trnP.
        eapply fold_right_idempotent_aux_one.
        exact fassoc.
        exact fcom.
        intros ? ? ? Hx Hy.
        eapply fcong.
        exact Hy.
        intros ? ? Hx.
        eapply Ha;
        exact Hx.
        exact Hc.
        eapply IHx.
        exact fassoc.
        exact fcom.
        exact fcong.
        exact Ha.
        exact Hd.
    ++
      remember (filter (fun x => negb (eqP a x)) Y) as 
        remove_a_Y.
      (* There is no a in remove_a_Y *)
      assert(Hd: in_set eqP remove_a_Y a = false).
      subst; eapply in_set_false.

      (* There is a, in fact one, 'a' in Y*)
      assert(He : in_set eqP Y a = true).  
        eapply brel_set_elim_prop in Hb;
        try assumption.
        destruct Hb as [Hbl Hbr].
        eapply Hbl.
        cbn; eapply bop_or_intro.
        left. apply refP.
      
      assert(Hg : brel_set eqP X remove_a_Y = true).
        rewrite Heqremove_a_Y.
        eapply brel_set_filter;
        try assumption.
      (* Specialise the induction hypothesis *)
      pose proof IHx remove_a_Y p f fassoc fcom fcong Ha Hg as Hh.
      (* 
        I need to play with transitivity. 
      *)
      eapply trnP.
      eapply fcong.
      eapply refP.
      exact Hh.
      eapply symP.
      eapply trnP.
      (* Now I am in a bit better situation. *)
      eapply fold_right_in_set.
      exact fassoc.
      exact fcom.
      exact fcong.
      exact Ha.
      exact He.
      rewrite <-Heqremove_a_Y.
      eapply fcong.
      all:eapply refP.
Qed.
      



Lemma fold_left_simp : 
  forall (X : list (A * P))
    (pa : A) (pb : P),
  fold_left 
    (λ '(s1, t1) '(_, t2), (s1, addP t1 t2)) 
    X (pa, pb) =  
    (pa, fold_left (λ t1 t2, addP t1 t2) 
    (List.map snd X ) pb).
Proof.
  induction X as [|(a,b) X IHx].
  + simpl; reflexivity.
  + simpl; intros ? ?.
    rewrite IHx.
    reflexivity.
Qed.

Lemma map_in_set :
  forall (X : list (A * P)) (au av : A)
  (bu bv : P), 
  eqA au av = true ->
  eqP bu bv = true ->
  (av, bv) [in] X ->
  in_set eqA (map fst X) au = true ∧
  in_set eqP (map snd X) bu = true.
Proof.
  induction X as [|(ux, vx) X IHx];
  simpl.
  +
    intros ? ? ? ? Ha Hb Hc.
    congruence.
  +
    intros ? ? ? ? Ha Hb Hc.
    eapply bop_or_elim in Hc.
    split.
    ++ 
      eapply bop_or_intro.
      destruct Hc as [Hc | Hc].
      eapply bop_and_elim in Hc.
      firstorder.
      right.
      exact (proj1 (IHx _ _ _ _ Ha Hb Hc)).
    ++
      eapply bop_or_intro.
      destruct Hc as [Hc | Hc].
      eapply bop_and_elim in Hc.
      left. firstorder.
      right.
      exact (proj2 (IHx _ _ _ _ Ha Hb Hc)).
Qed.






Lemma length_filter {T : Type} : 
  forall (X : list T) (f : T -> bool),
  (length (filter f X) < S (length X))%nat.
Proof.
  induction X as [| ax X IHx];
  simpl.
  +
    intros ?.
    nia.
  +
    intros ?.
    destruct (f ax);
    simpl.
    ++
      specialize (IHx f).
      nia.
    ++
      specialize (IHx f).
      nia.
Qed.



Lemma membship_filter : 
  forall (Y X : list (A * P)) (ax : A)
  (bx : P),
  (ax, bx) :: X =S= Y ->
  Y =S= (ax, bx) :: 
  filter (λ p : A * P, 
  negb (brel_product eqA eqP p (ax, bx))) Y.
Proof.
  intros ? ? ? ? Ha.
  eapply brel_set_intro_prop;
  try assumption.
  eapply refAP.
  eapply brel_set_elim_prop in Ha;
  [|apply symAP | apply trnAP].
  destruct Ha as [Hal Har].
  split.
  +
    intros (au, av) Hb.
    apply in_set_cons_intro;
    [apply symAP |].
    case_eq (eqP bx av);
    case_eq (eqA ax au);
    intros Hc Hd.
    ++
      left.
      eapply brel_product_intro;
      try assumption.
    ++
      right.
      eapply in_set_filter_intro;
      [eapply symAP | eapply bop_neg_bProp_product_cong |].
      split.
      eapply Bool.negb_true_iff.
      unfold brel_product.
      apply symP in Hd.
      rewrite Hd.
      assert (He : eqA au ax = false).
      case_eq (eqA au ax); intro Hf.
      apply symA in Hf.
      rewrite Hf in Hc;
      congruence.
      reflexivity.
      rewrite He.
      compute;
      reflexivity.
      exact Hb.
    ++
      right.
      eapply in_set_filter_intro;
      [eapply symAP | eapply bop_neg_bProp_product_cong |].
      split.
      eapply Bool.negb_true_iff.
      unfold brel_product.
      apply symA in Hc.
      rewrite Hc.
      assert (He : eqP av bx = false).
      case_eq (eqP av bx); intro Hf.
      apply symP in Hf.
      rewrite Hf in Hd;
      congruence.
      reflexivity.
      rewrite He.
      compute;
      reflexivity.
      exact Hb.
    ++
      right.
      eapply in_set_filter_intro;
      [eapply symAP | eapply bop_neg_bProp_product_cong |].
      split.
      eapply Bool.negb_true_iff.
      unfold brel_product.
      assert (He : eqA au ax = false).
      case_eq (eqA au ax); intro Hf.
      apply symA in Hf.
      rewrite Hf in Hc;
      congruence.
      reflexivity.
      rewrite He.
      compute;
      reflexivity.
      exact Hb.
  +
    intros (au, av) Hb.
    apply in_set_cons_elim in Hb;
    [|apply symAP].
    case_eq (eqP bx av);
    case_eq (eqA ax au);
    intros Hc Hd.
    ++
      eapply Hal.
      eapply in_set_cons_intro;
      [eapply symAP |].
      left.
      unfold brel_product.
      rewrite Hc, Hd;
      compute; reflexivity.
    ++
      destruct Hb as [Hb | Hb].
      eapply brel_product_elim in Hb.
      destruct Hb as [Hb _].
      rewrite Hb in Hc;
      congruence.
      eapply in_set_filter_elim in Hb.
      exact (snd Hb).
      eapply bop_neg_bProp_product_cong.
    ++
      destruct Hb as [Hb | Hb].
      eapply brel_product_elim in Hb.
      destruct Hb as [_ Hb].
      rewrite Hb in Hd;
      congruence.
      eapply in_set_filter_elim in Hb.
      exact (snd Hb).
      eapply bop_neg_bProp_product_cong.
    ++
      destruct Hb as [Hb | Hb].
      eapply brel_product_elim in Hb.
      destruct Hb as [_ Hb].
      rewrite Hb in Hd;
      congruence.
      eapply in_set_filter_elim in Hb.
      exact (snd Hb).
      eapply bop_neg_bProp_product_cong.
Qed.


Lemma map_snd_filter_membership_true : 
  forall (X : list (A * P)) (ax : A) (bx : P),
  in_set eqP 
    (map snd (filter (λ (p : A * P), 
      negb (brel_product eqA eqP p (ax, bx))) X)) bx = true ->
    in_set eqP (map snd X) bx = true.
Proof.
  induction X as [|(au, av) X IHx];
  simpl.
  +
    intros ? ? Ha;
    congruence.
  +
    intros ? ? Ha.
    case_eq ((eqP av bx));
    case_eq ((eqA au ax));
    intros Hb Hc;
    rewrite Hb, Hc in Ha;
    simpl in Ha.
    ++
      apply symP in Hc.
      rewrite Hc;
      compute;
      reflexivity.
    ++
      apply symP in Hc.
      rewrite Hc;
      compute;
      reflexivity.
    ++
      assert (Hd : eqP bx av = false).
      case_eq (eqP bx av); intros Hf.
      apply symP in Hf;
      rewrite Hf in Hc;
      congruence.
      reflexivity.
      rewrite Hd in Ha |- *.
      simpl in * |- *.
      eapply IHx; exact Ha.
    ++
      assert (Hd : eqP bx av = false).
      case_eq (eqP bx av); intros Hf.
      apply symP in Hf;
      rewrite Hf in Hc;
      congruence.
      reflexivity.
      rewrite Hd in Ha |- *.
      simpl in * |- *.
      eapply IHx; exact Ha.
Qed.



Lemma in_set_filter_map_true_snd_forward : 
  forall (X : list (A * P)) (ax : A) (a bx : P),
  eqP bx a = false ->
  in_set eqP (map snd X) a = true ->
  in_set eqP
  (map snd (filter (λ p : A * P, 
    negb (brel_product eqA eqP p (ax, bx))) X)) a = true.
Proof.
  induction X as [|(au, av) X IHx];
  simpl.
  +
    intros ? ? ? Ha Hb.
    congruence.
  +
    intros ? ? ? Ha Hb.
    case_eq (in_set eqP (map snd X) a);
    case_eq (eqP a av); 
    intros Hc Hd; 
    rewrite Hc, Hd in Hb.
    ++
      simpl.
      case_eq ((eqP av bx));
      case_eq (eqA au ax);
      intros He Hf;
      simpl.
      *
        rewrite (symP _ _ (trnP _ _ _ Hc Hf)) in Ha;
        congruence.
      *
        rewrite Hc;
        compute;
        reflexivity.
      *
        rewrite Hc;
        compute;
        reflexivity.
      *
        rewrite Hc; 
        compute;
        reflexivity.
    ++
      case_eq ((eqP av bx));
      case_eq (eqA au ax);
      intros He Hf;
      simpl.
      *
        (* Induction Hypothesis *)
        eapply IHx;
        try assumption.
      *
        rewrite Hc;
        simpl.
        eapply IHx;
        try assumption.
      *
        rewrite Hc;
        simpl.
        eapply IHx;
        try assumption.
      *
        rewrite Hc;
        simpl.
        eapply IHx;
        try assumption.
      ++
        case_eq ((eqP av bx));
        case_eq (eqA au ax);
        intros He Hf;
        simpl.
        *
          rewrite (symP _ _ (trnP _ _ _ Hc Hf)) in Ha;
          congruence.
        *
          rewrite Hc;
          compute; 
          reflexivity.
        *
          rewrite Hc;
          compute; 
          reflexivity.
        * 
          rewrite Hc;
          compute; 
          reflexivity.
      ++
        simpl in Hb; 
        congruence.
Qed.



Lemma in_set_filter_map_true_snd_backward : 
  forall (X : list (A * P)) (ax : A) (a bx : P),
  eqP bx a = false ->
  in_set eqP
  (map snd (filter (λ p : A * P, 
    negb (brel_product eqA eqP p (ax, bx))) X)) a = true ->
  in_set eqP (map snd X) a = true. 
Proof.
  induction X as [|(au, av) X IHx];
  simpl.
  +
    intros ? ? ? Ha Hb;
    congruence.
  +
    intros ? ? ? Ha Hb.
    case_eq (eqP av bx);
    case_eq (eqA au ax);
    intros Hc Hd;
    rewrite Hc, Hd in Hb;
    simpl in Hb.
    ++
      eapply bop_or_intro.
      right.
      eapply IHx; 
      try assumption.
      exact Ha.
      exact Hb.
    ++
      eapply bop_or_elim in Hb.
      eapply bop_or_intro.
      destruct Hb as [Hb | Hb].
      left. exact Hb.
      right.
      eapply IHx;
      try assumption.
      exact Ha.
      exact Hb.
    ++
      eapply bop_or_elim in Hb.
      eapply bop_or_intro.
      destruct Hb as [Hb | Hb].
      left. exact Hb.
      right.
      eapply IHx;
      try assumption.
      exact Ha.
      exact Hb.
    ++
      eapply bop_or_elim in Hb.
      eapply bop_or_intro.
      destruct Hb as [Hb | Hb].
      left. exact Hb.
      right.
      eapply IHx;
      try assumption.
      exact Ha.
      exact Hb.
Qed.



Lemma brel_set_filter_product : 
  forall (X : list (A * P)) (ax : A)
  (bx : P),
  brel_set eqP (bx :: map snd X)
  (bx :: map snd (filter
    (λ (p : A * P), 
      negb (brel_product eqA eqP p (ax, bx))) X)) = true.
Proof.
  intros ? ? ?.
  eapply brel_set_intro_prop;
  try assumption.
  split.
  +
    intros ? Ha.
    eapply in_set_cons_elim in Ha;
    try assumption.
    eapply in_set_cons_intro;
    try assumption.
    case_eq (eqP bx a);
    intros Hb.
    left; exact eq_refl.
    right.
    destruct Ha as [Ha | Ha].
    rewrite Ha in Hb;
    congruence.
    eapply in_set_filter_map_true_snd_forward;
    try assumption.
  +
    intros ? Ha.
    eapply in_set_cons_elim in Ha;
    try assumption.
    eapply in_set_cons_intro;
    try assumption.
    case_eq (eqP bx a);
    intros Hb.
    left; reflexivity.
    right.
    destruct Ha as [Ha | Ha].
    rewrite Ha in Hb.
    congruence.
    eapply in_set_filter_map_true_snd_backward;
    try assumption.
    exact Hb.
    exact Ha.
Qed.





Lemma duplicate_an_element : 
  forall (Y Xt : list (A * P)) (ax : A)
  (bx : P),
  (ax, bx) :: Xt =S= Y ->
  brel_set eqP (map snd Y) (bx :: map snd Y) = true.
Proof.
    intros ? ? ? ? Ha.
    eapply brel_set_intro_prop;
    try assumption.
    eapply brel_set_elim_prop in Ha;
    [|eapply symAP| eapply trnAP].
    split.
    +
      intros ? Hb.
      eapply in_set_cons_intro;
      try assumption.
      right; exact Hb.
    +
      intros ? Hb.
      eapply in_set_cons_elim in Hb;
      try assumption.
      destruct Hb as [Hb | Hb].
      ++
        eapply in_set_right_congruence with bx;
        try assumption.
        destruct Ha as [Hal Har].
        pose proof Hal (ax, bx) as Hw.
        assert (Hv : (ax, bx) [in] (ax, bx) :: Xt).
        apply in_set_cons_intro;
        [eapply symAP | left].
        compute.
        rewrite refA, refP;
        reflexivity.
        specialize (Hw Hv).
        eapply map_in_set in Hw.
        destruct Hw as [Hwl Hwr].
        exact Hwr.
        apply refA.
        apply refP.
      ++
        exact Hb.
Qed.



(*
This turned out to be more tricky than 
I anticipated because now I can't 
do case analysis

Key to prove this lemma is staging a tricky 
induction principal that decreases on both components X and Y, 
contrary to structural induction. In addition, 
it also requires some key insight about transitivity. This 
equality is very difficult, yet fun at the same time, to 
work with. 
*)
Lemma map_preservs_equivalence_on_second : 
  forall X Y : list (A * P), 
  X =S= Y -> 
  brel_set eqP (List.map snd X) (List.map snd Y) = true.
Proof.
  intro X.
  refine ((fix Fn xs 
    (Hacc : (Acc (fun x y => 
      (List.length x < List.length y)%nat) xs)) 
    {struct Hacc} := _) X _).
  intros ? Ha.
  refine (match xs as xsp return xs = xsp -> _ with 
  | [] => _ 
  | (ax, bx) :: Xt => _ 
  end eq_refl); simpl; intros Hb.
  +
    rewrite Hb in Ha.
    eapply brel_set_nil  in Ha.
    rewrite Ha;
    compute; 
    reflexivity.
  +
    (* Induction case that involves 
      some tricky transitivity *)
    rewrite Hb in Ha.
    (* get rid of (ax, bx) from Xt *)
    remember (filter (λ p : A * P, 
      negb (brel_product eqA eqP p (ax, bx))) xs) as Xrem.
    (* get rid of all (ax, bx) from Y *)
    remember (filter (λ p : A * P, 
      negb (brel_product eqA eqP p (ax, bx))) Y) as Yrem.
    assert (Hc : Y =S= (ax, bx) :: Yrem).
    rewrite HeqYrem.
    eapply membship_filter;
    exact Ha.
    assert (Hd : Xrem =S= Yrem).
    rewrite HeqXrem, HeqYrem.
    eapply filter_congruence_gen;
    try assumption.
    eapply bop_neg_bProp_product_cong;
    try assumption.
    rewrite <-Hb in Ha;
    exact Ha.
    assert (He : Acc (fun x y => 
      (List.length x < List.length y)%nat) Xrem).
    eapply Acc_inv with xs;
    try assumption.
   
    rewrite HeqXrem, Hb;
    simpl.
    rewrite refA, refP;
    simpl.
    eapply length_filter.
    specialize (Fn Xrem He Yrem Hd) as Hf.
    (* 
      Here comes tricky transitivity 
    *)
    eapply brel_set_transitive with (bx :: map snd Yrem);
    try assumption.
    eapply brel_set_transitive with (bx :: (map snd Xrem));
    try assumption.
    ++
      rewrite HeqXrem.
      rewrite Hb;
      simpl.
      rewrite refA, refP;
      simpl.
      eapply brel_set_filter_product.
    ++
      eapply brel_set_intro_prop;
      try assumption.
      eapply brel_set_elim_prop in Hf;
      try assumption.
      destruct Hf as [Hfl Hfr].
      split.
      +++
        intros a Hg.
        eapply in_set_cons_elim in Hg;
        try assumption.
        eapply in_set_cons_intro; 
        try assumption.
        destruct Hg as [Hg | Hg].
        left; exact Hg.
        right.
        eapply Hfl;
        exact Hg.
      +++
        intros a Hg.
        eapply in_set_cons_elim in Hg;
        try assumption.
        eapply in_set_cons_intro; 
        try assumption.
        destruct Hg as [Hg | Hg].
        left; exact Hg.
        right.
        eapply Hfr;
        exact Hg.
    ++
      eapply brel_set_symmetric.
      (* duplicate a 'bx' in Y *)
      assert (Hg : brel_set eqP (map snd Y) 
        (bx :: map snd Y) = true).
      eapply duplicate_an_element;
      exact Ha.
      eapply brel_set_transitive with (bx :: map snd Y);
      try assumption.
      rewrite HeqYrem.
      eapply brel_set_filter_product.
    +
      eapply (Wf_nat.well_founded_ltof _ 
        (fun x => List.length x)).
Qed.


Lemma fold_left_right_symmetric_aux : 
  ∀ (U : Type) (eqU : brel U) (f : binary_op U),
    brel_reflexive U eqU -> 
    brel_symmetric U eqU ->
    brel_transitive U eqU -> 
    bop_associative U eqU f -> 
    bop_commutative U eqU f ->
    bop_congruence U eqU f ->
    ∀ (X : list U) (a ax : U),
    eqU (fold_right f (f a ax) X) (f ax (fold_right f a X)) = true.
Proof.
  intros * Href Hsym Htrn Hassoc Hcom Hcong.
  induction X as [|ah X IHx].
  +
    intros *; cbn.
    eapply Hcom.
  +
    intros *; cbn.
    specialize (IHx a ax).
    eapply Htrn with 
    (f ah (f ax (fold_right f a X))).
    ++
      remember ((fold_right f (f a ax) X)) as Xa.
      remember ((f ax (fold_right f a X))) as Xb.
      eapply Hcong;
      [eapply Href | exact IHx].
    ++
      remember ((fold_right f a X)) as Xa.
      eapply Htrn with (t := f (f ah ax) Xa);
      [eapply Hsym, Hassoc | eapply Hsym].
      eapply Htrn with (t := f (f ax ah) Xa);
      [eapply Hsym, Hassoc | eapply Hcong;
      [eapply Hcom | eapply Href]].
Qed.




Lemma fold_left_right_symmetric : 
  ∀ (U : Type) (eqU : brel U) (f : binary_op U),
    brel_reflexive U eqU -> 
    brel_symmetric U eqU ->
    brel_transitive U eqU -> 
    bop_associative U eqU f -> 
    bop_commutative U eqU f ->
    bop_congruence U eqU f ->
    ∀ (X : list U) (a : U),
    eqU (fold_left f X a) (fold_right f a X) = true.
Proof.
  intros * Href Hsym Htrn Hassoc Hcom. 
  induction X as [|ax X IHx].
  +
    intros *; cbn;
    eapply Href.
  +
    intros *; cbn.
    specialize (IHx (f a ax)).
    eapply Htrn;
    [exact IHx | eapply fold_left_right_symmetric_aux];
    try assumption.
Qed.



Lemma fold_left_congruence : 
  forall (X Y : list (A * P)) 
  (pa : A) (pb : P),
  (forall u v, (u, v) [in] X -> eqA u pa = true) ->
  (forall u v, (u, v) [in] Y -> eqA u pa = true) ->
  X =S= Y ->
  [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2)) 
    X (pa, pb)] =S= 
  [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2)) 
    Y (pa, pb)].
Proof.
  intros ? ? ? ? Ha Hb Hc.
  eapply  brel_set_elim_prop in Hc;
  [| apply symAP| apply trnAP].
  destruct Hc as [Hcl Hcr].
  repeat rewrite fold_left_simp.
  eapply  brel_set_intro_prop;
  [apply refAP | split].
  + intros (au, pu) Hd.
    apply bop_or_elim in Hd.
    destruct Hd as [Hd | Hd].
    apply brel_product_elim in Hd.
    destruct Hd as [Hdl Hdr].
    apply bop_or_intro.
    left.
    apply brel_product_intro.
    exact Hdl.
    eapply trnP.
    exact Hdr.
    (* start *)
    eapply trnP;
    [eapply fold_left_right_symmetric; auto |].
    eapply symP, trnP;
    [eapply fold_left_right_symmetric; auto |].
    eapply symP.
    (* end *)
    eapply fold_right_congruence.
    intros ? ? ?.
    eapply symP.
    eapply addP_assoc.
    eapply addP_com.
    intros ? ? ? ? Hxy Hwv;
    eapply cong_addP;
    try assumption.
    exact addP_gen_idempotent.
    apply map_preservs_equivalence_on_second.
    eapply brel_set_intro_prop.
    eapply refAP.
    split; assumption.
    inversion Hd.
  + 
    intros (au, pu) Hd.
    apply bop_or_elim in Hd.
    destruct Hd as [Hd | Hd].
    apply brel_product_elim in Hd.
    destruct Hd as [Hdl Hdr].
    apply bop_or_intro.
    left.
    apply brel_product_intro.
    exact Hdl.
    eapply trnP.
    exact Hdr.
    (* start *)
    eapply trnP;
    [eapply fold_left_right_symmetric; auto |].
    eapply symP, trnP;
    [eapply fold_left_right_symmetric; auto |].
    eapply symP.
    (* end *)
    eapply fold_right_congruence.
    intros ? ? ?;
    eapply symP;
    eapply addP_assoc.
    exact addP_com.
    intros ? ? ? ? Hxy Hwv;
    eapply cong_addP;
    try assumption.
    exact addP_gen_idempotent.
    apply map_preservs_equivalence_on_second.
    eapply brel_set_intro_prop.
    eapply refAP.
    split; assumption.
    inversion Hd.
Qed.



(* generalise this one *)
Lemma manger_merge_set_new_aux_fold_filter :
  ∀ (X Y : list (A * P)) (pa : A) (pb : P), 
  X =S= Y -> 
  [fold_left (λ '(s1, t1) '(_, t2), 
    (s1, addP t1 t2)) 
    (filter (λ '(s2, _), eqA pa s2) X) 
    (pa, pb)] =S= 
  [fold_left (λ '(s1, t1) '(_, t2), 
    (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA pa s2) Y) 
    (pa, pb)].
Proof.
  intros ? ? ? ? Ha.
  assert (Hb : theory.bProp_congruence _  
    (brel_product eqA eqP)
    (λ '(s2, _), eqA pa s2)).
  intros (aa, ap) (ba, bp) He.
  apply brel_product_elim in He.
  destruct He as [Hel Her].
  case_eq (eqA pa aa); intro Hf.
  rewrite (trnA pa aa ba Hf Hel);
  reflexivity.
  case_eq (eqA pa ba); intro Hg.
  apply symA in Hel.
  rewrite (trnA pa ba aa Hg Hel) in Hf;
  congruence.
  reflexivity.
  pose proof filter_congruence_gen 
    X Y (λ '(s2, _), eqA pa s2) Hb Ha as Hc.
  remember (filter (λ '(s2, _), eqA pa s2) X) 
  as Xf.
  remember (filter (λ '(s2, _), eqA pa s2) Y) 
  as Yf.
  eapply fold_left_congruence.
  + intros ? ? Hd.
    rewrite HeqXf in Hd.
    eapply in_set_filter_elim in Hd;
    firstorder.
  + intros ? ? Hd.
    rewrite HeqYf in Hd.
    eapply in_set_filter_elim in Hd;
    firstorder.
  + exact Hc.
Qed. 


  


Lemma append_congruence : 
  forall X₁ X₂ Y₁ Y₂ : list (A * P), 
  X₁ =S= Y₁ -> 
  X₂ =S= Y₂ ->
  X₁ ++ X₂ =S= Y₁ ++ Y₂.
Proof.
  intros ? ? ? ? Ha Hb.
  apply brel_set_elim_prop in Ha, Hb;
  try (repeat apply symAP; repeat apply trnAP).
  destruct Ha as [Hal Har].
  destruct Hb as [Hbl Hbr].
  apply brel_set_intro_prop.
  apply refAP.
  split.
  + intros (a, b) Hc.
    apply in_set_concat_elim in Hc.
    destruct Hc as [Hc | Hc].
    apply in_set_concat_intro.
    left.
    apply Hal; exact Hc.
    apply in_set_concat_intro.
    right.
    apply Hbl; exact Hc.
    apply symAP.
  + intros (a, b) Hc.
    apply in_set_concat_elim in Hc.
    destruct Hc as [Hc | Hc].
    apply in_set_concat_intro.
    left.
    apply Har; exact Hc.
    apply in_set_concat_intro.
    right.
    apply Hbr; exact Hc.
    apply symAP.
Qed.

Local Notation "[MMSN]"  := 
  (manger_merge_sets_new eqA addP).

Lemma manger_merge_set_new_congruence_left :
  ∀ X Y p, 
  X =S= Y -> [MMSN] X p =S= [MMSN] Y p.
Proof.
  unfold manger_merge_sets_new,
  manger_merge_sets_new_aux.
  intros ? ? (pa, pb) Ha; cbn.
  pose proof 
    (manger_merge_set_new_aux_congruence_left X Y pa Ha) as 
    [Hb Hc].
  eapply append_congruence;
  [exact Hb | 
    eapply manger_merge_set_new_aux_fold_filter;
    exact Ha].
Qed.

(* [MMS] and [MMSN] are same *)
Lemma manger_merge_set_manger_merge_set_new_same :
  forall X p, [MMS] X p = [MMSN] X p.
Proof.
  unfold manger_merge_sets_new,
  manger_merge_sets_new_aux.
  induction X as [|(a, b) X Ihx].
  + simpl;
    intros ?; reflexivity.
  + simpl.
    intros (pa, pb); simpl.
    case_eq (eqA pa a); intro Ha;
    simpl.
    ++
      rewrite Ihx;
      reflexivity.
    ++
      f_equal.
      rewrite Ihx;
      reflexivity.
Qed.


Lemma manger_merge_set_congruence_left :
  ∀ Y Y' p, Y =S= Y' -> ([MMS] Y p) =S= ([MMS] Y' p).
Proof.
  intros ? ? ? Ha.
  repeat rewrite manger_merge_set_manger_merge_set_new_same.
  apply manger_merge_set_new_congruence_left;
  exact Ha.
Qed.

Lemma uop_manger_phase1_auxiliary_congurence_left :
  ∀ X Y1 Y2,  Y1 =S= Y2 -> [P1AX] Y1 X =S= [P1AX] Y2 X. 
Proof. induction X; intros Y1 Y2 H1; simpl. 
       - exact H1. 
       - assert (H2 := manger_merge_set_congruence_left _ _ a H1). 
         apply IHX; auto.
Qed.



Lemma  fst_unique_in_set_implies_manger_merge_set_fixpoint : 
∀ Y a' p', fst_unique_in_set ((a', p') :: Y) -> ([MMS] Y (a',p')) =S= ((a', p') :: Y). 
Proof. induction Y; intros a' p' H1; simpl. 
       - apply refSetAP. 
       - destruct a as [a p].
         case_eq(eqA a' a); intro H2.
         + case_eq(eqP p' p); intro H7.
           * assert (H3 : ((a', p') :: (a, p) :: Y) =S= ((a', p') :: Y)).
             {
               assert (H4 : (a', p') == (a, p)).
               {
                 apply brel_product_intro; auto. 
               } 
               exact (remove_duplicate_from_set Y _ _ H4). 
             } 
             assert (H4 : fst_unique_in_set ((a', p') :: Y)).
             {
               exact (fst_unique_in_set_congruence _ _ H3 H1). 
             } 
             assert (H5 := IHY _ _ H4).
             apply symSetAP in H3.
             assert (H6 := trnSetAP _ _ _ H5 H3).
             assert (H8 := cong_addP _ _ _ _(refP p') H7).
             assert (H9 := idemP p'). apply symP in H9.
             assert (H10 := trnP _ _ _ H9 H8).
             assert (H11 : (a', addP p' p) == (a', p')).
             {
               apply brel_product_intro; auto. 
             }
             assert (H12 : [MMS] Y (a', addP p' p) =S= [MMS] Y (a', p')).
             {
               exact(manger_merge_set_congruence_right Y _ _ H11). 
             } 
             exact(trnSetAP _ _ _ H12 H6). 
           * apply fst_unique_in_set_cons_elim in H1.
             destruct H1 as [H1 H3]. 
             apply fst_unique_in_set_cons_elim in H3.
             destruct H3 as [H3 H4].
             assert (H5 : (a, p) [in] (a, p) :: Y).
             {
               apply in_set_cons_intro.
               -- apply symAP.
               -- left. apply brel_product_intro.
                  apply refA. apply refP. 
             } 
             assert (H6 := H1 _ _ H5).
             destruct H6 as [H6 | H6].
             -- apply brel_product_elim in H6.
                destruct H6 as [_ H6].
                rewrite H6 in H7. discriminate H7. 
             -- rewrite H6 in H2. discriminate H2. 
         + assert (H3 : (a, p) :: (a', p') :: Y =S= (a', p') :: (a, p) :: Y).
           {
             apply set_rearrange_v1. 
           } 
           assert (H4 : fst_unique_in_set ((a', p') :: Y)).
           {
             apply symSetAP in H3. 
             assert (H5 := fst_unique_in_set_congruence _ _ H3 H1).
             apply fst_unique_in_set_cons_elim in H5.
             destruct H5 as [_ H5].
             exact H5. 
           } 
           assert (H5 := IHY _ _ H4).
           assert (H6 : (a, p) :: ([MMS] Y (a', p')) =S= (a, p) :: (a', p') :: Y).
           {
             exact (set_equal_with_cons_right _ _ (a, p) H5). 
           } 
           exact (trnSetAP _ _ _ H6 H3). 
Qed. 
         
Lemma  fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint_general : 
∀ X Y, fst_unique_in_set (X ++ Y) -> ([P1AX] Y X) =S= (X ++ Y). 
Proof. induction X; intros Y H1.
       - simpl.
         apply brel_set_reflexive; auto.
         + apply refAP. 
         + apply symAP.          
       - destruct a as [a p].
         rewrite <- app_comm_cons in H1.
         rewrite <- app_comm_cons. simpl.
         assert (H4 : (a, p) :: X ++ Y =S= X ++ (a, p) :: Y). 
         {
           apply set_rearrange_v2. 
         } 
         assert (H2: fst_unique_in_set (X ++ ((a, p) :: Y))).
         {
           exact (fst_unique_in_set_congruence _ _ H4 H1). 
         } 
         assert (H3 := IHX _ H2).
         assert (H3' : fst_unique_in_set ((a, p) :: Y)).
         {
           exact (fst_unique_in_set_concat_elim_right _ _ H2). 
         } 
         assert (H4' : ([MMS] Y (a, p)) =S= ((a, p) :: Y)).
         {
           exact (fst_unique_in_set_implies_manger_merge_set_fixpoint _ _ _ H3'). 
         } 
         assert (H5 : [P1AX] ([MMS] Y (a, p)) X =S= [P1AX] ((a, p) :: Y) X).
         {
           exact (uop_manger_phase1_auxiliary_congurence_left _ _ _ H4'). 
         }
         apply symSetAP in H4. 
         exact (trnSetAP _ _ _ (trnSetAP _ _ _ H5 H3) H4). 
Qed. 

             
Lemma  fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint : 
∀ X, fst_unique_in_set X -> ([P1AX] nil X) =S= X. 
Proof. intro X.
       assert (H1 := fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint_general X nil).
       rewrite app_nil_r in H1.
       exact H1. 
Qed. 

Lemma uop_manger_phase_1_auxiliary_uop_idempotent :
  ∀ X Y,  fst_unique_in_set Y -> [P1AX] nil ([P1AX] Y X) =S= [P1AX] Y X. 
Proof. intros X Y H1.
       assert (H2 := uop_manger_phase_1_auxiliary_preserves_uniqueness X Y H1).
       apply fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint; auto. 
Qed. 

Lemma fst_unique_in_empty_set : fst_unique_in_set nil.
Proof. intros a a' p p' H. compute in H. discriminate H. Qed.

Lemma uop_manger_phase_1_uop_idempotent : uop_idempotent _ [EQ] [P1]. 
Proof. intro X. unfold uop_manger_phase_1.
       apply uop_manger_phase_1_auxiliary_uop_idempotent.
       apply fst_unique_in_empty_set. 
Qed. 

Lemma uop_manger_phase_2_uop_idempotent : uop_idempotent _ [EQ] [P2]. 
Proof. intro X. unfold uop_manger_phase_2.  
       apply uop_minset_idempotent.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
       - apply manger_pre_order_congruence. 
       - apply manger_pre_order_reflexive.
Qed.          


Lemma in_set_uop_manger_phase_1_aux_lemma : 
  forall (X : finite_set (A * P)) 
  (a : A) (p : P),
  in_set  (brel_product eqA eqP) 
    (uop_manger_phase_1 eqA addP X) (a, p) = true ->
  X <> nil.
Proof.
  destruct X as [|(ax, ay) X];
  simpl.
  +
    intros ? ? Ha.
    congruence.
  +
    intros ? ? Ha Hb.
    congruence.
Qed.


Lemma  manger_pre_order_below_congruence : 
  brel_congruence (A * P) (brel_product eqA eqP)
  (manger_pre_order (below eqA)).
Proof.
  unfold manger_pre_order.
  apply brel_product_congruence.
  eapply below_congruence; assumption.
  compute; intros; reflexivity.
Qed.



Lemma manger_merge_set_funex : [MMS] = [MMSN].
Proof.
  eapply FunctionalExtensionality.functional_extensionality;
  intros X.
  eapply FunctionalExtensionality.functional_extensionality;
  intros x.
  eapply manger_merge_set_manger_merge_set_new_same.
Qed.
  


Lemma existence_non_empty : 
  forall (X : finite_set (A * P)) 
  (a : A),
  (∃ q : P, (a, q) [in] X) -> X <> nil.
Proof.
  destruct X as [|(ax, bx) X];
  simpl; intro a;
  intros [q Ha] Hb;
  congruence.
Qed.
 


(* Needed to reconsile between 
  Coq filter and filter defined 
  in our library *)
Lemma list_filter_lib_filter_same : 
  forall (X : finite_set (A * P))
  (f : A * P -> bool), 
  List.filter f X = filter f X.
Proof.
  induction X as [|(ax, bx) X IHx];
  simpl.
  +
    intros ?;
    reflexivity.
  +
    intros ?.
    case_eq (f (ax, bx));
    intro Ha.
    f_equal.
    eapply IHx.
    eapply IHx.
Qed.


Lemma filter_equality : 
  forall (X : finite_set (A * P))
  (a au : A), 
  eqA a au = true ->
  filter (λ '(s2, _), eqA a s2) X = 
  filter (λ '(s2, _), eqA au s2) X.
Proof.
  induction X as [|(ax, ay) X IHx];
  intros ? ? Ha; simpl.
  + reflexivity.
  + 
    case_eq (eqA a ax);
    case_eq (eqA au ax);
    intros Hc Hb.
    ++
      f_equal.
      eapply IHx;
      assumption.
    ++
      eapply symA in Ha.
      rewrite (trnA _ _ _ Ha Hb) in Hc.
      congruence.
    ++
      rewrite (trnA _ _ _ Ha Hc) in Hb.
      congruence.
    ++
      eapply IHx;
      try assumption.
Qed.

Lemma filter_equality_negb : 
  forall (X : finite_set (A * P))
  (a au : A), 
  eqA a au = true ->
  filter (λ '(s2, _), negb (eqA a s2)) X = 
  filter (λ '(s2, _), negb (eqA au s2)) X.
Proof.
  induction X as [|(ax, ay) X IHx];
  intros ? ? Ha; simpl.
  + reflexivity.
  + 
    case_eq (eqA a ax);
    case_eq (eqA au ax);
    intros Hc Hb.
    ++
      f_equal.
      eapply IHx;
      assumption.
    ++
      eapply symA in Ha.
      rewrite (trnA _ _ _ Ha Hb) in Hc.
      congruence.
    ++
      rewrite (trnA _ _ _ Ha Hc) in Hb.
      congruence.
    ++
      cbn.
      f_equal.
      eapply IHx;
      try assumption.
Qed.

Lemma filter_filter : 
  forall (V: finite_set (A * P))
  (a b : A),
  eqA a b = false ->
  List.filter (λ '(x, _), eqA a x) 
  (List.filter (λ '(s2, _), negb (eqA b s2)) V) =
  List.filter (λ '(x, _), eqA a x) V.
Proof.
  induction V as [|(au, av) V IHv];
  simpl; intros ? ? Ha.
  + reflexivity.
  +
    case_eq (eqA b au);
    case_eq (eqA a au);
    intros Hc Hb;
    cbn.
    ++
      apply symA in Hb.
      rewrite (trnA _ _ _ Hc Hb) in Ha.
      congruence.
    ++
      eapply IHv;
      assumption.
    ++
      rewrite Hc.
      f_equal.
      eapply IHv;
      assumption.
    ++
      rewrite Hc.
      eapply IHv;
      assumption.
Qed.
    

Lemma fold_left_filter : 
  forall (V : finite_set (A * P))
  (au : A) (av : P),
  (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA au s2) V) (au, av)) ==
  (au, fold_left (λ t1 t2 : P, addP t1 t2) 
      (map snd (List.filter (λ '(x, _), eqA au x) V)) av).
Proof.
  induction V as [|(ax, ay) V IHv];
  simpl; intros ? ?.
  + eapply bop_and_intro;
    [eapply refA | eapply refP].
  +
    case_eq (eqA au ax); 
    intro Ha.
    cbn.
    exact (IHv au (addP av ay)).
    exact (IHv au av).
Qed.
  


Lemma mmsn_invariant_sum_fn : 
  forall (V: finite_set (A * P))
  (a au : A) (av : P),
  eqA a au = false ->
  eqP 
  (sum_fn zeroP addP snd 
    (List.filter (λ '(x, _), eqA a x) ([MMSN] V (au, av))))
  (sum_fn zeroP addP snd 
    (List.filter (λ '(x, _), eqA a x) V)) = true.
Proof.
  unfold manger_merge_sets_new,
  manger_merge_sets_new_aux;
  cbn.
  intros ? ? ? ? Ha.
  rewrite <-list_filter_lib_filter_same,
    filter_app, filter_filter;
  try assumption.
  eapply trnP with 
    (addP 
      (sum_fn zeroP addP snd (List.filter (λ '(x, _), eqA a x) V))
      (sum_fn zeroP addP snd 
      (List.filter (λ '(x, _), eqA a x)
       [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
         (filter (λ '(s2, _), eqA au s2) V) (au, av)]))).
  eapply sum_fn_distributes_over_concat;
  try assumption.
  split;
  [exact (zeropLid s) | exact (zeropRid s)].
  assert (Hb : fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
  (filter (λ '(s2, _), eqA au s2) V) (au, av) == 
  (au, fold_left (λ t1 t2 : P, addP t1 t2) 
  (map snd (List.filter (λ '(x, _), eqA au x) V)) av)).
  eapply fold_left_filter.
  cbn.
  destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
  (filter (λ '(s2, _), eqA au s2) V) (
  au, av)) as (x, y) eqn:Hc.
  eapply brel_product_elim in Hb.
  destruct Hb as [Hbl Hbr].
  assert (Hd : eqA a x = false).
  case_eq (eqA a x);
  intro Hd.
  rewrite (trnA _ _ _ Hd Hbl) in Ha;
  congruence.
  reflexivity.
  rewrite Hd;
  cbn.
  eapply zeropRid.
Qed.




(* This lemma should be sum_fn *)
Lemma fold_right_zero : 
  forall (X : finite_set P)
  (av : P),
  eqP (fold_right (λ t1 t2 : P, addP t1 t2) av X)
  (addP av 
  (fold_right (λ t1 t2 : P, addP t1 t2) zeroP X)) = true.
Proof.
  induction X as [|ax X IHx];
  intros ?; cbn.
  +
    eapply symP,
    zeropRid.
  +
    specialize (IHx av).
    remember ((fold_right (λ t1 t2 : P, addP t1 t2) av X)) as Xa.
    remember (fold_right (λ t1 t2 : P, addP t1 t2) zeroP X) as Xb.
    assert (Ha : eqP ((addP av (addP ax Xb))) 
    (addP (addP av ax) Xb) = true).
    eapply symP, addP_assoc.
    eapply trnP with (addP (addP av ax) Xb).
    assert (Hb : eqP 
    (addP (addP ax av) Xb) 
    (addP (addP av ax) Xb) = true).
    eapply cong_addP;
    [eapply addP_com | eapply refP].
    eapply trnP with (addP (addP ax av) Xb).
    eapply trnP with (addP ax (addP av Xb)).
    eapply cong_addP;
    [eapply refP | exact IHx].
    eapply symP, addP_assoc.  
    exact Hb.
    eapply symP.
    exact Ha.
Qed.



Lemma mmsn_invariant : 
  forall Ub V a au av, 
    a <A> au -> 
  eqP
  (sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA a x) Ub ++
      List.filter (λ '(x, _), eqA a x) ([MMSN] V (au, av))))
  (sum_fn zeroP addP snd 
    (List.filter (λ '(x, _), eqA a x)
      (Ub ++ V))) = true.
Proof.
  intros ? ? ? ? ? Ha.
  eapply trnP with 
  (sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA a x) Ub ++
      List.filter (λ '(x, _), eqA a x) V)).
  eapply trnP with 
  (addP (sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA a x) Ub))
    (sum_fn zeroP addP snd 
      (List.filter (λ '(x, _), eqA a x) ([MMSN] V (au, av))))).
  eapply sum_fn_distributes_over_concat;
  try assumption.
  split;
  [eapply zeropLid | eapply zeropRid].
  eapply trnP with 
    (addP (sum_fn zeroP addP snd (List.filter (λ '(x, _), eqA a x) Ub))
     (sum_fn zeroP addP snd
        (List.filter (λ '(x, _), eqA a x) V))).
  eapply cong_addP.
  eapply refP.
  eapply mmsn_invariant_sum_fn;
  exact Ha.
  eapply symP.
  apply sum_fn_distributes_over_concat;
  try assumption.
  split;
  [eapply zeropLid | eapply zeropRid].
  rewrite filter_app.
  eapply refP.
Qed.
  

Lemma eqP_fold_right_refl : 
  forall V a au, 
  eqA a au = true ->
  eqP (fold_right addP zeroP (map snd (List.filter (λ '(x, _), eqA au x) V)))
  (fold_right addP zeroP (map snd (List.filter (λ '(x, _), eqA a x) V))) =
  true.
Proof.
  induction V as [|(ax, bx) V IHv];
  intros ? ? Ha; cbn.
  +
    eapply refP.
  +
    case_eq (eqA au ax);
    intro Hb.
    ++
      rewrite (trnA _ _ _ Ha Hb).
      cbn.
      eapply cong_addP;
      [eapply refP| eapply IHv].
      exact Ha.
    ++
      case_eq (eqA a ax);
      intro Hc.
      rewrite (trnA _ _ _ (symA _ _ Ha) Hc) in Hb;
      congruence.
      eapply IHv.
      exact Ha.
Qed.
      




Lemma fold_right_distributes : 
  forall U V,
  eqP (fold_right addP zeroP (U ++ V))
  (addP (fold_right addP zeroP U) (fold_right addP zeroP V)) = true.
Proof.
  induction U as [|u U IHu];
  intros ?.
  +
    cbn; eapply symP.
    eapply zeropLid.
  +
    cbn.
    eapply symP.
    remember ((fold_right addP zeroP U)) as Ua.
    remember ((fold_right addP zeroP V)) as Va.
    remember ((fold_right addP zeroP (U ++ V))) as UVa.
    eapply trnP with 
      (addP u (addP Ua Va)).
    eapply addP_assoc.
    eapply cong_addP.
    eapply refP.
    eapply symP.
    specialize (IHu V); subst.
    exact IHu.
Qed.


Lemma filter_filter_negb : 
  forall (V : finite_set (A * P)) ax au, 
  eqA au ax = true ->
  List.filter (λ '(s2, _), negb (eqA ax s2))
    (filter (λ '(s2, _), negb (eqA au s2)) V) = 
  List.filter (λ '(s2, _), negb (eqA ax s2)) V.
Proof.
  induction V as [|(a, b) V IHv];
  simpl; intros ? ? Ha;
  [exact eq_refl|].
  case_eq (eqA au a);
  intros Hb.
  +
    simpl.
    rewrite (trnA _ _ _ (symA _ _ Ha) Hb);
    simpl.
    eapply IHv.
    exact Ha.
  +
    simpl.
    assert (Hc : eqA ax a = false).
    case_eq (eqA ax a); 
    intros Hc.
    rewrite (trnA _ _ _ Ha Hc) in Hb;
    congruence.
    reflexivity.
    rewrite Hc.
    cbn. 
    f_equal.
    eapply IHv.
    exact Ha.
Qed.


Lemma filter_empty : 
  forall (V : finite_set (A * P))
  au ax, 
  eqA au ax = true -> 
  List.filter (λ '(s2, _), eqA ax s2)
  (List.filter (λ '(s2, _), negb (eqA au s2)) V) = [].
Proof.
  induction V as [|(a, b) V IHv];
  simpl; 
  intros ? ? Ha;
  [exact eq_refl|].
  case_eq (eqA au a);
  intros Hb; cbn;
  [eapply IHv; assumption |].
  case_eq (eqA ax a);
  intros Hc.
  rewrite (trnA _ _ _ Ha Hc) in Hb;
  congruence.
  eapply IHv;
  assumption.
Qed.

Lemma push_add_outside : 
  forall V av bx y yt, 
  eqP y (fold_left (λ t1 t2 : P, addP t1 t2) V av) = true ->
  eqP yt (fold_left (λ t1 t2 : P, addP t1 t2) V (addP av bx)) = true ->
  eqP (addP bx y) yt = true.
Proof.
  intros ? ? ? ? ? Ha Hb.
  
  (* start *)
  assert (Hal : eqP y (fold_right (λ t1 t2 : P, addP t1 t2) av V) = true).
  eapply trnP;
  [eapply Ha| eapply fold_left_right_symmetric; auto].
  clear Ha; rename Hal into Ha.
  assert (Hbl : eqP yt
    (fold_right (λ t1 t2 : P, addP t1 t2) (addP av bx) V) = true).
  eapply trnP;
  [eapply Hb| eapply fold_left_right_symmetric; auto].
  clear Hb; rename Hbl into Hb.
  (* end *)

  assert (Hc : 
    eqP y (addP av (fold_right (λ t1 t2 : P, addP t1 t2) zeroP V)) = true).
  eapply trnP;
  [exact Ha| eapply fold_right_zero].
  clear Ha.
  assert (Hd : 
    eqP yt (addP (addP av bx) 
    (fold_right (λ t1 t2 : P, addP t1 t2) zeroP V)) = true).
  eapply trnP;
  [exact Hb | eapply fold_right_zero].
  clear Hb.
  remember ((fold_right (λ t1 t2 : P, addP t1 t2) zeroP V)) as Vt.
  assert (Ha : eqP yt (addP (addP bx av) Vt) = true).
  eapply trnP.
  exact Hd.
  eapply cong_addP.
  eapply addP_com.
  eapply refP.
  clear Hd.
  assert (Hb : eqP yt (addP bx (addP av Vt)) = true).
  eapply trnP.
  exact Ha.
  eapply addP_assoc.
  clear Ha.
  eapply trnP with (addP bx (addP av Vt)).
  eapply cong_addP;
  [eapply refP | exact Hc].
  eapply symP;
  exact Hb.
Qed.


(* Properties related to in_set. Think about it *)
Lemma mmsn_same_add : 
  forall V au av ax bx, 
  eqA au ax = true ->
  ([MMSN] ([MMSN] V (au, av)) (ax, bx))  =S=
  ([MMSN] V (au, addP av bx)).
Proof.
  intros ? ? ? ? ? Ha.
  eapply brel_set_intro_prop;
  [eapply refAP|].
  split.
  + 
    intros (a, p) Hb.
    eapply in_set_concat_elim in Hb.
    eapply in_set_concat_intro.
    destruct Hb as [Hb | Hb];
    simpl in * |- * .
    cbn in Hb.
    repeat rewrite <-list_filter_lib_filter_same,
    filter_app, filter_filter_negb in Hb.
    eapply in_set_concat_elim in Hb.
    destruct Hb as [Hb | Hb].
    left.
    rewrite list_filter_lib_filter_same in Hb.
    erewrite filter_equality_negb.
    exact Hb.
    exact Ha.
    rewrite list_filter_lib_filter_same in Hb.
    assert (Hc : fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA au s2) V) (
    au, av) == (au, fold_left (λ t1 t2 : P, addP t1 t2) 
    (map snd (List.filter (λ '(x, _), eqA au x) V)) av)).
    eapply fold_left_filter.
    destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA au s2) V) (
    au, av)) as (x, y) eqn:Hd.
    eapply brel_product_elim in Hc.
    destruct Hc as [Hcl Hcr].
    cbn in Hb.
    rewrite (trnA _ _ _ (symA _ _ Ha) (symA _ _ Hcl)) in Hb;
    cbn in Hb;
    congruence.
    eapply symAP.
    exact Ha.
    eapply bop_or_elim in Hb.
    destruct Hb as [Hb | Hb].
    ++
      cbn in Hb.
      repeat rewrite <-list_filter_lib_filter_same in Hb.
      rewrite filter_app, filter_empty, app_nil_l in Hb.
      assert (Hc : fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA au s2) V) (
      au, av) == (au, fold_left (λ t1 t2 : P, addP t1 t2) 
      (map snd (List.filter (λ '(x, _), eqA au x) V)) av)).
      eapply fold_left_filter.
      destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA au s2) V) (
      au, av)) as (x, y) eqn:Hd.
      eapply brel_product_elim in Hc.
      destruct Hc as [Hcl Hcr].
      rewrite <-list_filter_lib_filter_same in Hd.
      rewrite Hd in Hb.
      cbn in Hb.
      rewrite (trnA _ _ _ (symA _ _ Ha) (symA _ _ Hcl)) in Hb;
      cbn in Hb.
      eapply bop_and_elim in Hb.
      destruct Hb as [Hbl Hbr].
      right.
      eapply bop_or_intro; left.
      assert (He : fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA au s2) V) (
      au, addP av bx) == (au, fold_left (λ t1 t2 : P, addP t1 t2) 
      (map snd (List.filter (λ '(x, _), eqA au x) V)) (addP av bx))).
      eapply fold_left_filter.
      destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA au s2) V) (
      au, addP av bx)) as (xt, yt) eqn:Hf.
      eapply brel_product_elim in He.
      destruct He as [Hel Her].
      eapply bop_and_intro.
      eapply trnA with au.
      exact (trnA _ _ _ Hbl (symA _ _ Ha)).
      eapply symA; assumption.
      remember ((map snd (List.filter (λ '(x, _), eqA au x) V))) as Vt.
      eapply trnP with (addP bx y);
      try assumption.
      (* pull out the bx from Her to the front, 
      use congruence and then Hcr *)
      (* More algebraic manipulation! *)
      eapply push_add_outside;
      [exact Hcr | exact Her].
      exact Ha.
    ++
      congruence.
    ++
      eapply symAP.
  +
    intros (a, p) Hb.
    eapply in_set_concat_elim in Hb.
    eapply in_set_concat_intro.
    destruct Hb as [Hb | Hb].
    left; simpl.
    cbn.
    erewrite <-list_filter_lib_filter_same,
    filter_app, filter_filter_negb.
    eapply in_set_concat_intro.
    left; cbn in Hb;
    erewrite list_filter_lib_filter_same, 
    filter_equality_negb.
    exact Hb. eapply symA; exact Ha.
    exact Ha.
    right.
    eapply in_set_cons_elim in Hb.
    eapply in_set_cons_intro;
    [eapply symAP|].
    destruct Hb as [Hb | Hb].
    left.
    cbn in Hb.
    assert (He : fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA au s2) V) (
      au, addP av bx) == (au, fold_left (λ t1 t2 : P, addP t1 t2) 
      (map snd (List.filter (λ '(x, _), eqA au x) V)) (addP av bx))).
    eapply fold_left_filter.
    destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA au s2) V) (
    au, addP av bx)) as (xt, yt) eqn:Hf.
    eapply brel_product_elim in He.
    destruct He as [Hel Her].
    cbn.
    repeat rewrite <-list_filter_lib_filter_same.
    rewrite filter_app, 
    filter_empty, app_nil_l.
    assert (Hc : fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA au s2) V) (
      au, av) == (au, fold_left (λ t1 t2 : P, addP t1 t2) 
      (map snd (List.filter (λ '(x, _), eqA au x) V)) av)).
    eapply fold_left_filter.
    destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA au s2) V) (
    au, av)) as (x, y) eqn:Hd.
    eapply brel_product_elim in Hc.
    destruct Hc as [Hcl Hcr].
    repeat rewrite list_filter_lib_filter_same.
    rewrite Hd.
    cbn. 
    assert (Hg : eqA ax x = true).
    case_eq (eqA ax x);
    intros Hg;
    [exact eq_refl |].
    rewrite (trnA _ _ _ (symA _ _ Ha) (symA _ _ Hcl)) in 
    Hg; congruence.
    rewrite Hg.
    cbn.
    eapply bop_and_intro.
    eapply brel_product_elim in Hb.
    destruct Hb as [Hbl Hbr].
    (* it's good idea to write a proof search in 
    Ltac or Coq-elpi *)
    eapply trnA with au.
    eapply symA; assumption.
    exact (trnA _ _ _ (symA _ _ Hel) Hbl).
    eapply brel_product_elim in Hb.
    destruct Hb as [Hbl Hbr].
    eapply trnP with yt;
    try assumption.
    remember (map snd (List.filter (λ '(x, _), eqA au x) V)) as Vt.
    (* A lot of algebraic manipulation! *)
    eapply push_add_outside;
    [exact Hcr | exact Her].
    exact Ha.
    simpl in Hb; congruence.
    all:eapply symAP.
Qed.


Lemma filter_filter_curry : 
  forall (V : finite_set (A * P)) au ax, 
  List.filter (λ '(s2, _), negb (eqA ax s2))
  (List.filter (λ '(s2, _), negb (eqA au s2)) V) = 
  List.filter (λ '(s2, _), 
    bop_and (negb (eqA ax s2)) (negb (eqA au s2))) V.
Proof.
  induction V as [|(a, b) V IHv];
  simpl; intros ? ?;
  [exact eq_refl|].
  case_eq (eqA au a); 
  intros Hb.
  +
    cbn;
    rewrite Bool.andb_false_r;
    eapply IHv; 
    try assumption.
  +
    cbn.
    case_eq (eqA ax a);
    intro Hc;
    cbn.
    eapply IHv.
    f_equal.
    eapply IHv.
Qed.

Lemma filter_bop_and_comm : 
  forall (V : finite_set (A * P)) au ax, 
  List.filter (λ '(s2, _), 
    bop_and (negb (eqA ax s2)) (negb (eqA au s2))) V = 
  List.filter (λ '(s2, _), 
    bop_and (negb (eqA au s2)) (negb (eqA ax s2))) V.
Proof.
  induction V as [|(a, b) V IHv];
  simpl; intros ? ?;
  [exact eq_refl|].
  unfold bop_and.
  rewrite Bool.andb_comm, 
  IHv; exact eq_refl.
Qed.
    


Lemma mmsn_diff_swap_first : 
  forall V au av ax bx a b,
  eqA au ax = false ->
  eqA a au = true ->
  [MMSN] ([MMSN] ((a, b) :: V) (au, av)) (ax, bx) =S= 
  [MMSN] ([MMSN] V (au, addP av b)) (ax, bx).
Proof.
  intros ? ? ? ? ? ? ? Ha Hb;
  cbn.
  rewrite (symA _ _ Hb);
  cbn.
  eapply brel_set_reflexive.
  eapply refAP.
  eapply symAP.
Qed.



Lemma mmsn_diff_swap_second : 
  forall V au av ax bx a b,
  eqA au ax = false ->
  eqA a au = true ->
  [MMSN] ([MMSN] ((a, b) :: V) (ax, bx)) (au, av) =S= 
  [MMSN] ([MMSN] V (ax, bx)) (au, addP av b).
Proof.
  intros * Ha Hb.
  cbn.
  assert (Hc : eqA ax a = false).
  case_eq (eqA ax a);
  intros Hc.
  rewrite (trnA _ _ _ (symA _ _ Hb) (symA _ _ Hc)) in Ha;
  congruence.
  reflexivity.
  rewrite Hc; cbn.
  rewrite (symA _ _ Hb); cbn.
  eapply brel_set_reflexive.
  eapply refAP.
  eapply symAP.
Qed.

Lemma mmsn_diff_swap_third : 
  forall V au av ax bx a b,
  eqA au ax = false ->
  eqA a au = false ->
  eqA a ax = true -> 
  [MMSN] ([MMSN] ((a, b) :: V) (ax, bx)) (au, av) =S= 
  [MMSN] ([MMSN] V (ax, addP bx b)) (au, av).
Proof.
  intros * Ha Hb Hc.
  cbn;
  rewrite (symA _ _ Hc); cbn.
  eapply brel_set_reflexive.
  eapply refAP.
  eapply symAP.
Qed.

Lemma mmsn_diff_swap_fourth : 
  forall V au av ax bx a b,
  eqA au ax = false ->
  eqA a au = false ->
  eqA a ax = true -> 
  [MMSN] ([MMSN] ((a, b) :: V) (au, av)) (ax, bx) =S= 
  [MMSN] ([MMSN] V (au, av)) (ax, addP bx b).
Proof.
  intros * Ha Hb Hc.
  cbn.
  case_eq (eqA au a);
  intro Hd.
  rewrite (symA _ _ Hd) in Hb;
  congruence.
  cbn.
  rewrite (symA _ _ Hc); cbn.
  eapply brel_set_reflexive.
  eapply refAP.
  eapply symAP.
Qed.



(* Think about it. This proof is more trickier than 
I thought!  *)
Lemma mmsn_diff_swap : 
  forall V au av ax bx, 
  eqA au ax = false -> 
  ([MMSN] ([MMSN] V (au, av)) (ax, bx)) =S= 
  ([MMSN] ([MMSN] V (ax, bx)) (au, av)).
Proof.
  induction V as [|(a, b) V IHv];
  intros ? ? ? ? Ha.
  + 
    cbn; rewrite Ha; 
    cbn.
    case_eq (eqA ax au);
    intros Hb; cbn.
    rewrite (symA _ _ Hb) in Ha;
    congruence.
    eapply brel_set_intro_prop;
    [eapply refAP|]; split;
    intros (a, p) Hc.
    eapply in_set_cons_elim in Hc;
    [|eapply symAP].
    eapply in_set_cons_intro;
    [eapply symAP|].
    destruct Hc as [Hc | Hc].
    right.
    eapply in_set_cons_intro;
    [eapply symAP|left; assumption].
    eapply in_set_cons_elim in Hc;
    [|eapply symAP].
    destruct Hc as [Hc | Hc].
    left; assumption.
    simpl in Hc; congruence.
    eapply in_set_cons_elim in Hc;
    [|eapply symAP].
    eapply in_set_cons_intro;
    [eapply symAP|].
    destruct Hc as [Hc | Hc].
    right.
    eapply in_set_cons_intro;
    [eapply symAP|left; assumption].
    eapply in_set_cons_elim in Hc;
    [|eapply symAP].
    destruct Hc as [Hc | Hc].
    left; assumption.
    simpl in Hc; congruence.
  +
    case_eq (eqA a au);
    intros Hb.
    ++
      (* a = au *)
      (* we move things and we are home *)
      eapply brel_set_transitive;
      [eapply refAP | eapply symAP | eapply trnAP | | ].
      eapply  mmsn_diff_swap_first; 
      try assumption.
      eapply brel_set_symmetric.
      eapply brel_set_transitive;
      [eapply refAP | eapply symAP | eapply trnAP | | ].
      eapply mmsn_diff_swap_second; 
      try assumption.
      eapply IHv. 
      case_eq (eqA ax au);
      intro Hc.
      rewrite (symA _ _ Hc) in Ha;
      congruence.
      reflexivity.
    ++
      (* a <> au *)
      case_eq (eqA a ax);
      intros Hc.
      +++
        (* a <> au ∧ a = ax *)
        (* we move thing and we are home *)
        eapply brel_set_symmetric.
        eapply brel_set_transitive;
        [eapply refAP | eapply symAP | eapply trnAP | | ].
        eapply mmsn_diff_swap_third; 
        try assumption.
        eapply brel_set_symmetric.
        eapply brel_set_transitive;
        [eapply refAP | eapply symAP | eapply trnAP | | ].
        eapply mmsn_diff_swap_fourth; 
        try assumption.
        eapply IHv; assumption.
      +++
        (* a <> au ∧ a <> ax *)
        cbn.
        assert (Hd : eqA au a = false).
        case_eq (eqA au a);
        intro Hd;
        [rewrite (symA _ _ Hd) in Hb; 
        congruence | reflexivity].
        repeat rewrite Hd; cbn.
        assert (He :  eqA ax a = false).
        case_eq (eqA ax a);
        intro He;
        [rewrite (symA _ _ He) in Hc; 
        congruence | reflexivity].
        repeat rewrite He; cbn.
        rewrite Hd; cbn.
        eapply set_equal_with_cons_right.
        exact (IHv au av ax bx Ha).
Qed.        


(* This is too general and may be difficult to prove.
Wow, I can't believe it turned out to be such a nice proof!
*)
Lemma fold_left_in_set_mmsn_cong : 
  forall U V W a p, 
  V =S= W ->  
  (a, p) [in] fold_left [MMSN] U V ->
  (a, p) [in] fold_left [MMSN] U W.
Proof.
  induction U as [|(ax, bx) U IHu].
  +
    cbn.
    intros ? ? ? ? Ha Hb.
    eapply brel_set_elim_prop in Ha.
    destruct Ha as [Hal Har].
    eapply Hal; exact Hb.
    eapply symAP.
    eapply trnAP.
  +
    simpl.
    intros ? ? ? ? Ha Hb.
    pose proof manger_merge_set_congruence_left V W (ax, bx) Ha as Hc.
    rewrite manger_merge_set_funex in Hc.
    eapply IHu;
    [exact Hc | exact Hb].
Qed.


(* Difficult to prove! *)
Lemma mmsn_sum : 
  forall (U V : finite_set (A * P))
  (au a : A) (av p : P),
  eqA a au = true ->
  eqP p (addP av (fold_right addP zeroP 
    (map snd (filter (λ '(x, _), eqA a x) (U ++ V))))) = true ->
    (a, p) [in] fold_left [MMSN] U ([MMSN] V (au, av)).
Proof.
  induction U as [|(ax, bx) U IHu];
  intros ? ? ? ? ? Ha Hb.
  +
    cbn.
    (* go right *)
    eapply in_set_concat_intro.
    right.
    eapply in_set_cons_intro;
    [eapply symAP| left].
    cbn in Hb.
    eapply brel_product_transitive with 
    (au, fold_left (λ t1 t2 : P, addP t1 t2) 
      (map snd (List.filter (λ '(x, _), eqA au x) V)) av);
    try assumption.
    rewrite <-list_filter_lib_filter_same.
    pose proof fold_left_filter V au av as Hc.
    rewrite <-list_filter_lib_filter_same in Hc.
    exact Hc.
    eapply brel_product_intro;
    [eapply symA in Ha; exact Ha|].
    
    (* start  *)
    eapply trnP.
    eapply fold_left_right_symmetric; auto.
    (* end *)

    rewrite <-list_filter_lib_filter_same in Hb.
    eapply trnP with (addP av
    (fold_right addP zeroP
       (map snd (List.filter (λ '(x, _), eqA au x) V)))).
    eapply fold_right_zero.
    eapply symP.
    rewrite <-Hb.
    eapply cong_eqP;
    [eapply refP|].
    eapply cong_addP;
    [eapply refP| eapply eqP_fold_right_refl].
    exact Ha.
  +
    simpl in * |- *.
    (* case analysis *)
    case_eq (eqA a ax);
    intro Hc.
    ++
      assert (Hd : eqA au ax = true).
      rewrite (trnA _ _ _ (symA _ _ Ha) Hc);
      exact eq_refl.
      eapply fold_left_in_set_mmsn_cong with 
        (V := ([MMSN] V (au, addP av bx))).
      eapply brel_set_symmetric.
      eapply mmsn_same_add.
      exact Hd.
      rewrite Hc in Hb.
      simpl in Hb.
      eapply IHu;
      try assumption.
      rewrite <-Hb.
      eapply cong_eqP;
      [eapply refP|].
      eapply addP_assoc.
    ++
      (* a <A> ax *)
      rewrite Hc in Hb.
      eapply fold_left_in_set_mmsn_cong with  
        (V := ([MMSN] ([MMSN] V (ax, bx)) (au, av))).
      eapply brel_set_symmetric.
      eapply mmsn_diff_swap.
      case_eq (eqA au ax);
      intro Hd.
      rewrite (trnA _ _ _ Ha Hd) in Hc.
      congruence.
      reflexivity.
      eapply IHu;
      try assumption.
      rewrite <-Hb.
      eapply cong_eqP;
      [eapply refP|].
      eapply cong_addP;
      [eapply refP|].
      repeat rewrite <-list_filter_lib_filter_same.
      repeat rewrite filter_app,
      map_app.
      remember (map snd (List.filter (λ '(x, _), eqA a x) U)) as Ua.
      remember (map snd (List.filter (λ '(x, _), eqA a x) ([MMSN] V (ax, bx)))) as Va.
      remember (map snd (List.filter (λ '(x, _), eqA a x) V)) as Vb.
      eapply trnP with 
        (addP (fold_right addP zeroP Ua)
          (fold_right addP zeroP Va)).
      eapply fold_right_distributes.
      eapply symP.
      eapply trnP with 
      (addP (fold_right addP zeroP Ua) (fold_right addP zeroP Vb)).
      eapply fold_right_distributes.
      remember ((fold_right addP zeroP Ua)) as Uaa.
      remember ((fold_right addP zeroP Vb)) as Vbb.
      remember ((fold_right addP zeroP Va)) as Vaa.
      eapply cong_addP.
      eapply refP.
      subst.
      eapply symP.
      eapply mmsn_invariant_sum_fn;
      assumption.
Qed.





Lemma in_set_fold_left_mmsn_intro : 
  forall (U V : finite_set (A * P))
    (a : A) (p : P),
    (∃ q : P, (a, q) [in] U) -> 
    eqP p (sum_fn zeroP addP snd 
      (filter (λ '(x, _), eqA a x) 
        (U ++ V))) = true ->
    (a, p) [in] fold_left [MMSN] U V.
Proof.
  induction U as [|(au, av) U IHu];
  simpl.
  + intros ? ? ? [_ Ha] Hb.
    congruence.
  +
    intros ? ? ? [q Ha] Hb.
    (* Check if U is empty or not?
      But don't simplify it *)
    destruct U as [|(bu, bv) U].
    ++
      cbn in Ha, Hb.
      eapply bop_or_elim in Ha.
      destruct Ha as [Ha | Ha].
      +++
        (* Looks true except I need to 
          prove some complicated lemma 
        *)
        (* Difficult but true *)
        eapply bop_and_elim in Ha.
        destruct Ha as (Hal & Har).
        rewrite Hal in Hb.
        cbn in Hb.
        unfold manger_merge_sets_new,
        manger_merge_sets_new_aux.
        cbn.
        eapply in_set_concat_intro.
        right.
        remember ((filter (λ '(x, _), 
          eqA a x) V)) as Va.
        remember ((filter (λ '(s2, _),
          eqA au s2) V)) as Vb.
        assert (Hc : Va = Vb).
        rewrite HeqVa, HeqVb.
        eapply filter_equality;
        assumption.
        rewrite Hc in Hb.
        rewrite fold_left_simp.
        eapply in_set_singleton_intro.
        eapply symAP.
        eapply brel_product_intro.
        eapply symA; exact Hal.
        eapply symP.
        (* start  *)
        eapply symP, trnP.
        eapply fold_left_right_symmetric; auto.
        eapply symP.
        (* end *)
        pose proof fold_right_zero (map snd Vb) av 
        as Hd.
        eapply symP in Hd.
        exact (trnP _ _ _ Hb Hd).
      +++
        congruence.
    ++
      (* Induction case *)
      remember ((bu, bv) :: U) as Ub.
      case_eq (eqA a au);
      case_eq (eqP q av);
      case_eq (in_set (brel_product eqA eqP) Ub (a, q));
      intros He Hd Hc;
      rewrite Hc, Hd, He in Ha;
      cbn in Ha.
      +++
        rewrite Hc in Hb;
        cbn in Hb.
        eapply  mmsn_sum;
        try assumption.
      +++
        rewrite Hc in Hb;
        cbn in Hb.
        eapply  mmsn_sum;
        try assumption.
      +++
        rewrite Hc in Hb; 
        cbn in Hb.
        eapply  mmsn_sum;
        try assumption.
      +++
        congruence.
      +++
        rewrite Hc in Hb.
        (* inductive case *)
        eapply IHu.
        exists q;
        exact He.
        rewrite <-list_filter_lib_filter_same.
        rewrite filter_app.
        eapply trnP with 
        (sum_fn zeroP addP snd 
        (List.filter (λ '(x, _), eqA a x) (Ub ++ V))).
        rewrite list_filter_lib_filter_same.
        exact Hb.
        eapply symP. 
        eapply mmsn_invariant.
        exact Hc.
      +++
        congruence.
      +++
        rewrite Hc in Hb;
        cbn in Hb.
        eapply IHu.
        exists q;
        exact He.
        rewrite <-list_filter_lib_filter_same.
        rewrite filter_app.
        eapply trnP with 
        (sum_fn zeroP addP snd 
        (List.filter (λ '(x, _), eqA a x) (Ub ++ V))).
        rewrite list_filter_lib_filter_same.
        exact Hb.
        eapply symP. 
        eapply mmsn_invariant.
        exact Hc.
      +++
        congruence.
Qed.




Lemma in_set_fold_left_mmsn_intro_forall : 
  forall (U V : finite_set (A * P))
  (a : A) (p : P) (q : P),
  (a, q) [in] U -> 
  eqP p (sum_fn zeroP addP snd 
    (filter (λ '(x, _), eqA a x) 
      (U ++ V))) = true ->
  (a, p) [in] fold_left [MMSN] U V.
Proof.
  intros * Ha Hb.
  eapply in_set_fold_left_mmsn_intro.
  exists q; exact Ha.
  exact Hb.
Qed.



      
Lemma in_set_uop_manger_phase_1_intro : 
  forall (X : finite_set (A * P)) 
  (a : A) (p : P),
  (∃ q : P, (a, q) [in] X) ->
  eqP p (sum_fn zeroP addP snd 
    (List.filter (λ '(x, _), eqA x a) X)) = true -> 
  in_set (brel_product eqA eqP) 
    (uop_manger_phase_1 eqA addP X) (a, p) = true.
Proof.
  intros ? ? ? [q Ha] Hb.
  unfold uop_manger_phase_1, 
  manger_phase_1_auxiliary.
  rewrite manger_merge_set_funex.
  (* 
    First thing: 
    generalise the [] to Y because it will 
    make the induction hypothesis stronger, 
    otherwise it is impossible to prove this, 
    at least from my experience.
  *)
  eapply in_set_fold_left_mmsn_intro.
  +
    exists q;
    exact Ha.
  +
    rewrite app_nil_r.
    rewrite list_filter_lib_filter_same in Hb.
    assert (Hc : (filter (λ '(x, _), eqA a x) X) =
    filter (λ '(x, _), eqA x a) X).
    f_equal. 
    eapply FunctionalExtensionality.functional_extensionality;
    intros (ax, bx).
    case_eq (eqA a ax);
    case_eq (eqA ax a);
    intros Hc Hd;
    try reflexivity.
    eapply symA in Hd;
    rewrite Hc in Hd;
    congruence.
    eapply symA in Hc; 
    rewrite Hc in Hd;
    congruence.
    rewrite Hc;
    exact Hb.
  Qed.

Lemma in_set_concat_rewrite :
  forall (X Y : finite_set (A * P)) a p , 
  in_set (brel_product eqA eqP) (X ++ Y) (a, p) = 
  (in_set (brel_product eqA eqP) X (a, p) || 
  in_set (brel_product eqA eqP) Y (a, p))%bool.
Proof.
  induction X as [|(au, bu) X IHx].
  +
    intros *.
    cbn; reflexivity.
  +
    intros *.
    cbn.
    rewrite IHx.
    remember ((bop_and (eqA a au) (eqP p bu))) as ax.
    remember (in_set (brel_product eqA eqP) X (a, p)) as bx.
    remember (in_set (brel_product eqA eqP) Y (a, p)) as cx. 
    destruct ax, bx, cx; simpl; reflexivity.
Qed.
    
Lemma in_set_not_membership: 
  forall (Y : finite_set (A * P)) a p au, 
  a <A> au -> 
  in_set (brel_product eqA eqP) 
    (filter (λ '(s2, _), negb (eqA au s2)) Y) (a, p) 
  = 
  in_set (brel_product eqA eqP) Y (a, p).
Proof.
  induction Y as [|(ax, bx) Y IHy].
  +
    intros * Ha.
    cbn; reflexivity.
  +
    intros * Ha.
    cbn.
    case_eq (eqA au ax);
    intros Hb; cbn.
    rewrite IHy.
    assert (Hc : eqA a ax = false).
    case_eq (eqA a ax);
    intros Hc.
    rewrite (trnA _ _ _ Hc (symA _ _ Hb)) in Ha; 
    congruence.
    reflexivity.
    rewrite Hc; reflexivity.
    assumption.
    rewrite IHy.
    reflexivity.
    exact Ha.
Qed.
    


Lemma mmsn_diff_swap_gen : 
  forall(V : finite_set (A * P)) 
  (au : A) (av : P) (ax : A) (bx : P),
  ([MMSN] ([MMSN] V (au, av)) (ax, bx)) =S= 
  ([MMSN] ([MMSN] V (ax, bx)) (au, av)).
Proof.
  intros *.
  case_eq (eqA ax au);
  intro Ha.
  +
    (* eqA ax au = true *)
    pose proof mmsn_same_add V au av ax bx (symA _ _ Ha) as Hb.
    pose proof mmsn_same_add V ax bx au av Ha as Hc.
    eapply brel_set_transitive with 
    ([MMSN] V (au, addP av bx));
    [eapply refAP | eapply symAP | eapply trnAP | 
    exact Hb|].
    eapply brel_set_symmetric, 
    brel_set_transitive with ([MMSN] V (ax, addP bx av));
    [eapply refAP | eapply symAP | eapply trnAP | 
    exact Hc|].
    repeat rewrite <-manger_merge_set_manger_merge_set_new_same.
    eapply manger_merge_set_congruence_right.
    eapply brel_product_intro.
    exact Ha.
    eapply addP_com.
  +
    assert (Hb : au <A> ax).
    case_eq (eqA au ax);
    intro Hb;
    [rewrite (symA _ _ Hb) in Ha;
    congruence | exact eq_refl]. 
    pose proof mmsn_diff_swap V au av ax bx Hb as Hc.
    pose proof mmsn_diff_swap V ax bx au av Ha as Hd.
    eapply brel_set_transitive with 
    ([MMSN] ([MMSN] V (ax, bx)) (au, av));
    [eapply refAP | eapply symAP | eapply trnAP | exact Hc | ].
    eapply brel_set_reflexive;
    [exact refAP | exact symAP].
Qed.

(* This was an awesome find!
*)
Lemma bop_and_in_list_rewrite_tricky {U : Type} 
  {r : brel U}
  {symU : brel_symmetric U r}
  {trnU : brel_transitive U r} : 
  forall (Y : list U) (au a : U),
  in_list r Y au = false ->
  in_list r Y a = true ->
  r a au = false.
Proof.
  induction Y as [|ax Y IHy].
  +
    intros * Ha Hb.
    cbn in Hb.
    congruence.
  +
    intros * Ha Hb.
    cbn in Ha, Hb.
    eapply Bool.orb_false_iff in Ha.
    eapply Bool.orb_true_iff in Hb.
    destruct Ha as (Hal & Har).
    destruct Hb as [Hb | Hb].
    ++
      case_eq (r a au);
      intros Hc.
      rewrite (trnU _ _ _ (symU _ _ Hc) Hb) in Hal;
      congruence.
      reflexivity.
    ++
      eapply IHy; try assumption.
Qed.



Fixpoint no_dup {U : Type} (r : brel U) 
  (X : finite_set U) : bool := 
 match X with 
 | [] => true
 | h :: t => bop_and (negb (in_list r t h))
  (no_dup r t)
 end.




Lemma in_set_false_membership_aux :
  forall (U V  : finite_set (A * P)) a p,
  U =S= V -> 
  in_set (brel_product eqA eqP) V (a, p) = false ->
  in_set (brel_product eqA eqP) U (a, p) = false.
Proof.
  intros * Ha Hb.
  eapply brel_set_elim_prop in Ha;
  [|exact symAP|exact trnAP];
  destruct Ha as (Hal & Har);
  revert dependent V; revert p; revert a;
  induction U as [|(au, bu) U IHu].
  +
    intros * Ha Hb Hc;
    reflexivity.
  +
    (* induction case *)
    intros * Ha Hb Hc.
    cbn in * |- *.
    case_eq (eqA a au); intro Hd;
    case_eq (eqP p bu); intro He;
    case_eq ((in_set (brel_product eqA eqP) U (a, p))); 
    intro Hf;
    cbn in * |- *;
    try reflexivity.
    ++
      
      specialize (Ha (au, bu)); 
      cbn in Ha; 
      rewrite refA, refP in Ha; 
      cbn in Ha.
      specialize (Ha eq_refl).
      pose proof in_set_right_congruence (A * P)
      (brel_product eqA eqP) symAP trnAP 
      (au, bu) (a, p) V as Hg.
      assert (Hh: (au, bu) == (a, p)).
      eapply brel_product_intro;
      [rewrite (symA _ _ Hd); exact eq_refl | 
      rewrite (symP _ _ He); exact eq_refl].
      specialize (Hg Hh Ha).
      rewrite Hg in Hc;
      congruence.
    ++
      specialize (Ha (au, bu)); 
      cbn in Ha; 
      rewrite refA, refP in Ha; 
      cbn in Ha.
      specialize (Ha eq_refl).
      pose proof in_set_right_congruence (A * P)
      (brel_product eqA eqP) symAP trnAP 
      (au, bu) (a, p) V as Hg.
      assert (Hh: (au, bu) == (a, p)).
      eapply brel_product_intro;
      [rewrite (symA _ _ Hd); exact eq_refl | 
      rewrite (symP _ _ He); exact eq_refl].
      specialize (Hg Hh Ha).
      rewrite Hg in Hc;
      congruence.
    ++
      (* contradiction *)
      specialize (Ha (a, p)).
      rewrite Hf in Ha;
      cbn in Ha;
      rewrite Hd, He in Ha;
      cbn in Ha.
      specialize (Ha eq_refl).
      rewrite Ha in Hc;
      congruence.
      (* contradiction using Ha and Hc *)
    ++
      specialize (Ha (a, p)).
      rewrite Hf in Ha;
      cbn in Ha;
      rewrite Hd, He in Ha;
      cbn in Ha.
      specialize (Ha eq_refl).
      rewrite Ha in Hc;
      congruence.
    ++
      specialize (Ha (a, p)).
      rewrite Hf in Ha;
      cbn in Ha;
      rewrite Hd, He in Ha;
      cbn in Ha.
      specialize (Ha eq_refl).
      rewrite Hc in Ha; 
      congruence.
Qed.




Lemma in_set_false_membership : 
  forall (X U V  : finite_set (A * P)) a p,
  U =S= V -> 
  in_set (brel_product eqA eqP) 
    (fold_left [MMSN] X V) (a, p) = false ->
  in_set (brel_product eqA eqP) 
    (fold_left [MMSN] X U) (a, p) = false.
Proof.
  induction X as [|(ax, bx) X IHx].
  +
    intros * Ha Hb.
    cbn in Hb |- *.
    eapply in_set_false_membership_aux;
    [exact Ha | exact Hb].
  +
    intros * Ha Hb.
    simpl in Hb |- *.
    exact (IHx ([MMSN] U (ax, bx))
    ([MMSN] V (ax, bx)) a p
    (manger_merge_set_new_congruence_left U V (ax, bx) Ha)
    Hb).
Qed.




Lemma in_set_mmsn : 
  forall (X U V  : finite_set (A * P)) a p,
  U =S= V -> 
  in_set (brel_product eqA eqP)
    (fold_left [MMSN] X U) (a, p) = 
  in_set (brel_product eqA eqP)
  (fold_left [MMSN] X V) (a, p).
Proof.
  intros * Ha.
  case_eq (in_set (brel_product eqA eqP) 
  (fold_left [MMSN] X V) (a, p)); intro Hb.
  eapply fold_left_in_set_mmsn_cong with (V := V).
  eapply brel_set_symmetric; exact Ha.
  exact Hb.
  eapply in_set_false_membership;
  [exact Ha | exact Hb].
Qed.



Lemma in_set_equality_false : 
  forall (X Y : finite_set (A * P))
  a p au av, 
  eqA a au = false ->
  in_set (brel_product eqA eqP) 
    (fold_left [MMSN] X ([MMSN] Y (au, av))) (a, p) 
  = 
  in_set (brel_product eqA eqP) 
    (fold_left [MMSN] X Y) (a, p).
Proof.
  (* 
    It's obviously True
  *)
  induction X as [|(ax, bx) X IHx].
  +
    simpl; intros * Ha.
    cbn.
    destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA au s2) Y) (au, av)) as (ux, vx) eqn:Hb.
    pose proof fold_left_filter Y au av as Hc.
    rewrite Hb in Hc.
    eapply brel_product_elim in Hc.
    destruct Hc as (Hcl & Hcr).
    rewrite in_set_concat_rewrite; cbn.
    assert (Hd : eqA a ux = false).
    case_eq (eqA a ux); intros Hd.
    rewrite (trnA _ _ _ Hd Hcl) in Ha;
    congruence.
    reflexivity.
    rewrite Hd; cbn. 
    rewrite Bool.orb_false_r.
    eapply in_set_not_membership; 
    try assumption.
    (*
      I can replace 
        in_set (brel_product eqA eqP)
        (filter (λ '(s2, _), negb (eqA au s2)) Y ++
          [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
            (filter (λ '(s2, _), eqA au s2) Y) (au, av)]) 
            (a, p) by 
        in_set (brel_product eqA eqP)
        (filter (λ '(s2, _), negb (eqA au s2)) Y) (a, p)
        Why? 
        Because 
        [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
            (filter (λ '(s2, _), eqA au s2) Y) (au, av)] = 
        [(au, ....)]

        Now, from 
        in_set (brel_product eqA eqP)
        (filter (λ '(s2, _), negb (eqA au s2)) Y) (a, p) = 
        in_set (brel_product eqA eqP) Y (a, p) should be trivial.  
    *)
  +
    simpl; intros * Ha.
    (* Look at the IHx. It is very general, 
    i.e., I can instantiate Y a p au av with anything 
    as long I have a proof a <A> au 
    
    I need to figure out some case analysis. 


      case analysis eqA ax a ?? 
      This is more tricky and may 
      require a lot of sublemmas
      if ax = a then we know that 
      ax <> au then by unfolding 
      and some rewriting, hopefully 
      we can discharge it

      ax <> a  
      Can I avoid comparing ax with au? 
      Otherwise, it's going to super annoying proof. 
    Can I infer for any au av ax bx, 
    ([MMSN] ([MMSN] Y (au, av)) (ax, bx))) =S=
    ([MMSN] ([MMSN] Y (ax, bx)) (au, av)))?
    *)
    pose proof  mmsn_diff_swap_gen Y au av ax bx as Hb.
    specialize (IHx ([MMSN] Y (ax, bx))  a p au av Ha) as Hc.
    eapply eq_trans.
    eapply in_set_mmsn.
    exact Hb.
    exact Hc.
Qed.
  



(* 
This one is not provable in its current form. 
However, if we change the goal to  
∃ q : P, (a, q) [in] (X ++ Y), then we can prove it.
*)
Lemma in_set_fold_left_mmsn_elim_first : 
  forall (X Y : finite_set (A * P))
    (a : A) (p : P),
    (a, p) [in] fold_left [MMSN] X Y ->
    ∃ q : P, (a, q) [in] (X ++ Y).
Proof.
  induction X as [|(au, av) X Ihx].
  +
    cbn.
    intros * Ha.
    eexists; exact Ha.
  +
    simpl.
    intros * Ha.
    case_eq (eqA a au);
    intros Hb.
    ++
     exists av.
     rewrite refP.
     cbn; reflexivity.
    ++
      cbn.
      rewrite in_set_equality_false in Ha.
      destruct (Ihx _ _ _ Ha) as (q & Hd).
      exists q.
      simpl; exact Hd.
      exact Hb.
Qed.



  


Lemma brel_list_refl : 
  forall Yt, 
  brel_list (brel_product eqA eqP) Yt Yt = true.
Proof.
  induction Yt; cbn; 
  [reflexivity| eapply bop_and_intro].
  eapply brel_product_reflexive;
  try assumption.
  exact IHYt.
Qed.

Ltac apply_in_Hyp_goal Hb := 
  eapply Bool.orb_false_iff in Hb; 
  eapply Bool.orb_false_iff;
  destruct Hb; repeat split;
  try assumption.


(* it should in library *)
Lemma bop_and_in_list_rewrite : 
  forall (Yt : list A) (a au : A),
  eqA a au = true ->
  in_list eqA Yt au = false ->
  in_list eqA Yt a = false.
Proof.
  induction Yt as [|b Y IHy].
  +
    intros * Ha Hb.
    cbn.
    reflexivity.
  +
    intros * Ha Hb.
    cbn in Hb |- *.
    apply_in_Hyp_goal Hb.
    case_eq (eqA a b);
    intros Hb.
    rewrite (trnA _ _ _ (symA _ _ Ha) Hb) in H;
    congruence.
    reflexivity.
    eapply IHy; 
    [exact Ha | exact H0].
Qed.
    



Lemma brel_inlist_membership : 
  ∀ (Yt X Y : list (A * P)) (a : A) (p : P),
  brel_list (brel_product eqA eqP) Yt (X ++ [(a, p)] ++ Y) = true ->
  in_list eqA (map fst Yt) a = true.
Proof.
  induction Yt as [|(au, bu) Yt IHyt].
  +
    intros * Ha.
    cbn in Ha |- *.
    destruct X; cbn in Ha; 
    congruence.
  +
    intros * Ha.
    cbn in Ha |- *.
    destruct X as [|(ux, uy) X].
    ++
      cbn in Ha.
      eapply bop_and_elim in Ha.
      destruct Ha as (Hal & Har).
      eapply bop_and_elim in Hal.
      destruct Hal as (Hall & Halr).
      case_eq (eqA a au); 
      intro Hb.
      reflexivity.
      rewrite (symA _ _ Hall) in Hb;
      congruence.
    ++
      cbn in Ha.
      eapply bop_and_elim in Ha.
      destruct Ha as (Hal & Har).
      eapply bop_and_elim in Hal.
      destruct Hal as (Hall & Halr).
      cbn in IHyt.
      rewrite (IHyt _ _ _ _ Har).
      now rewrite Bool.orb_true_r.
Qed.
      
    

(* This turns out to be more challenging than 
I anticipated! *)
Lemma nodup_inset : 
  forall (Y : finite_set (A * P))
  (a : A) (p : P),
  no_dup eqA (map fst Y) = true -> 
  (a, p) [in] Y -> 
  ∃ Y₁ Y₂, 
    brel_list (brel_product eqA eqP) Y (Y₁ ++ [(a, p)] ++ Y₂) = true ∧
    (in_list eqA (map fst Y₁) a = false) ∧
    (in_list eqA (map fst Y₂) a = false).
Proof.
  (* I need to thnk 
    when a = au then p has to match with 
    second component. 
    when a <> au then we don't care
  *)
  induction Y as [|(au, bu) Y IHy].
  +
    intros * Ha Hb.
    cbn in Hb; congruence.
  +
    intros * Ha Hb.
    cbn in Ha, Hb.
    eapply bop_and_elim in Ha.
    destruct Ha as (Hal & Har).
    eapply Bool.negb_true_iff in Hal.
    eapply bop_or_elim in Hb.
    (* destruct Y *)
    destruct Y as [| (auu, buu) Y].
    ++
      clear IHy;
      cbn in * |- .
      destruct Hb as [Hb | Hb];
      try congruence.
      exists [], [].
      cbn; repeat split; try reflexivity.
      eapply bop_and_elim in Hb.
      destruct Hb as [Hbl Hbr].
      rewrite (symA _ _ Hbl),
      (symP _ _ Hbr); reflexivity.
    ++
      (* inductive case *)
      remember ((auu, buu) :: Y) as Yt.
      destruct Hb as [Hb | Hb].
      +++
        exists [], Yt; cbn.
        apply bop_and_elim in Hb;
        destruct Hb as (Hbl & Hbr);
        rewrite (symA _ _ Hbl),
        (symP _ _ Hbr); cbn.
        repeat split; try reflexivity.
        eapply brel_list_refl.
        eapply bop_and_in_list_rewrite; 
        try assumption.
        exact Hbl. 
        exact Hal.
       
      +++
        destruct (IHy _ _ Har Hb) as 
        (Y₁ & Y₂ & Hd & He & Hf).
        exists ((au, bu) :: Y₁), Y₂;
        cbn.
        repeat split.
        rewrite refA, refP; 
        cbn; exact Hd.
        rewrite He.
        (* now the challenge *)
        (* I know that 
          au is not in Yt (from Hal) and 
          a is in Yt (from Hd )
          a <> au
        *)
        assert (Hg : in_list eqA (map fst Yt) a = true).
        eapply brel_inlist_membership; exact Hd.
        pose proof @bop_and_in_list_rewrite_tricky A 
          eqA symA trnA  _ _ _  Hal Hg as Hi.
        rewrite Hi; reflexivity.
        exact Hf.
Qed.
        

Lemma in_list_brel_cong_intro_gen : 
  forall (Y Y₁ Y₂ : list (A * P)) a,
  brel_list (brel_product eqA eqP) Y (Y₁ ++ Y₂) = true ->
  eqP (fold_right addP zeroP
     (map snd (filter (λ '(x, _), eqA x a) (Y₁ ++ Y₂))))
  (fold_right addP zeroP
     (map snd (filter (λ '(x, _), eqA x a) Y))) = true.
Proof.
  induction Y as [|(au, bu) Y IHy].
  +
    intros * Ha.
    cbn in Ha.
    destruct Y₁, Y₂; cbn 
    in Ha |- *; try assumption;
    try congruence.
  +
    intros * Ha.
    destruct Y₁ as [|(uy, vy) Y₁].
    ++
      destruct Y₂ as [|(uyy, vyy) Y₂].
      +++
        cbn in Ha; 
        congruence.
      +++
        cbn in Ha |- *.
        eapply bop_and_elim in Ha.
        destruct Ha as (Hal & Har).
        eapply bop_and_elim in Hal.
        destruct Hal as (Hall & Halr).
        case_eq (eqA au a);
        intro Hc.
        rewrite (trnA _ _ _ (symA _ _ Hall) Hc);
        cbn.
        specialize (IHy [] Y₂ a Har);
        cbn in IHy.
        eapply cong_addP; 
        try assumption.
        exact (symP _ _ Halr).
        assert (Hd : eqA uyy a = false).
        case_eq (eqA uyy a);
        intro Hd.
        rewrite (trnA _ _ _ Hall Hd) in Hc;
        congruence.
        reflexivity.
        rewrite Hd.
        exact (IHy [] Y₂ a Har).
    ++
      cbn in Ha |- *.
      eapply bop_and_elim in Ha.
      destruct Ha as (Hal & Har).
      eapply bop_and_elim in Hal.
      destruct Hal as (Hall & Halr).
      case_eq (eqA au a);
      intro Hc.
      rewrite (trnA _ _ _ (symA _ _ Hall) Hc);
      cbn.
      specialize (IHy Y₁ Y₂ a Har);
      cbn in IHy.
      eapply cong_addP; 
      try assumption.
      exact (symP _ _ Halr).
      assert (Hd : eqA uy a = false).
      case_eq (eqA uy a);
      intro Hd.
      rewrite (trnA _ _ _ Hall Hd) in Hc;
      congruence.
      reflexivity.
      rewrite Hd.
      exact (IHy Y₁ Y₂ a Har).
Qed.




Lemma in_list_brel_cong_intro : 
  forall (Y Y₁ Y₂ : list (A * P)) a p ,
  brel_list (brel_product eqA eqP) Y (Y₁ ++ Y₂) = true ->
  eqP p
  (fold_right addP zeroP
     (map snd (filter (λ '(x, _), eqA x a) (Y₁ ++ Y₂)))) = true ->
  eqP p
  (fold_right addP zeroP
     (map snd (filter (λ '(x, _), eqA x a) Y))) = true.
Proof.
  intros * Ha Hb.
  eapply trnP.
  exact Hb.
  eapply in_list_brel_cong_intro_gen.
  exact Ha.
Qed.






Lemma in_list_filter_empty : 
  forall (Y : list (A * P)) a, 
  in_list eqA (map fst Y) a = false -> 
  List.filter (λ '(x, _), eqA x a) Y = [].
Proof.
  induction Y as [|(ux, uy) Y IHy].
  +
    intros * Ha.
    cbn; reflexivity.
  +
    intros * Ha.
    cbn in Ha |- *.
    eapply Bool.orb_false_iff in Ha.
    destruct Ha as [Hal Har].
    case_eq (eqA ux a);
    intros Hb.
    rewrite (symA _ _ Hb) in Hal;
    congruence.
    eapply IHy; try assumption.
Qed.


Lemma in_list_false_membership :
  forall X Y a, 
  in_list eqA X a = false ->
  in_list eqA Y a = false ->
  in_list eqA (X ++ Y) a = false.
Proof.
  induction X as [|ax X IHx].
  +
    cbn; intros; assumption.
  +
    cbn; intros * Ha Hb.
    eapply Bool.orb_false_iff in Ha.
    destruct Ha as (Hal & Har).
    rewrite Hal; cbn.
    eapply IHx; try assumption.
Qed.



Lemma in_list_false_filter_membership : 
  forall (Y : finite_set (A * P)) au ax, 
  ax <A> au -> 
  in_list eqA (map fst Y) au = false ->
  in_list eqA (map fst 
  (filter (λ '(s2, _), negb (eqA ax s2)) Y)) au = false.
Proof.
  induction Y as [|(ah, bh) Y IHy].
  +
    cbn; intros; reflexivity.
  +
    cbn; intros * Ha Hb.
    eapply Bool.orb_false_iff in Hb.
    destruct Hb as (Hbl & Hbr).
    case_eq (eqA ax ah);
    intros Hc; cbn.
    eapply IHy; try assumption.
    rewrite Hbl; cbn.
    eapply IHy; try assumption.
Qed.


Lemma no_dup_filter : 
  forall (Y : finite_set (A * P)) ux ax,
  eqA ux ax = true ->
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst (filter (λ '(s2, _), negb (eqA ax s2)) Y) ++ [ux]) =
  true.
Proof.
  induction Y as [|(au, av) Y IHy].
  +
    intros * Ha Hb.
    cbn; reflexivity.
  +
    intros * Ha Hb.
    cbn in Hb |- *.
    eapply bop_and_elim in Hb.
    destruct Hb as (Hbl & Hbr).
    eapply Bool.negb_true_iff in Hbl.
    case_eq (eqA ax au);
    intros Hc; cbn.
    eapply IHy; assumption.
    eapply bop_and_intro.
    eapply Bool.negb_true_iff.
    eapply in_list_false_membership.
    eapply in_list_false_filter_membership; 
    try assumption.
    cbn. case_eq (eqA au ux);
    intro Hd.
    rewrite (trnA _ _ _ (symA _ _ Ha) (symA _ _ Hd)) in Hc;
    congruence.
    reflexivity.
    eapply IHy; assumption.
Qed.


Lemma no_dup_mmsn : 
  forall(Y : finite_set (A * P)) (ax : A) (bx : P), 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst ([MMSN] Y (ax, bx))) = true.
Proof.
  induction Y as [|(au, av) Y IHy].
  +
    intros * Ha.
    cbn; reflexivity.
  +
    intros * Ha.
    simpl in Ha |- *.
    eapply bop_and_elim in Ha.
    destruct Ha as (Hal & Har).
    eapply Bool.negb_true_iff in Hal.
    case_eq (eqA ax au);
    intro Hc.
    ++
      cbn; rewrite Hc; cbn.
      eapply IHy; try assumption.
    ++
      cbn.
      rewrite Hc; cbn.
      eapply bop_and_intro.
      eapply Bool.negb_true_iff.
      rewrite map_app.
      (* Wow, this is so annoying *)
      eapply in_list_false_membership.
      eapply in_list_false_filter_membership; 
      try assumption.
      cbn.
      rewrite Bool.orb_false_r.
      pose proof (fold_left_filter Y ax bx) as Hd.
      destruct ((fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA ax s2) Y) (ax, bx))) as 
      (ux, vx); cbn.
      eapply brel_product_elim in Hd.
      destruct Hd.
      case_eq (eqA au ux);
      intros Hd.
      rewrite (trnA _ _ _ (symA _ _ e) (symA _ _ Hd)) in Hc;
      congruence.
      reflexivity.
      rewrite map_app.
      destruct (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA ax s2) Y) (ax, bx)) as (ux, vx) eqn:Hd.
      pose proof (fold_left_filter Y ax bx) as He.
      rewrite Hd in He.
      eapply brel_product_elim in He.
      destruct He as (Hel & Her).
      cbn.
      eapply no_dup_filter; 
      try assumption.
Qed.


Lemma filter_arg_swap_gen : 
  forall (Y : finite_set (A * P)) ax a, 
  eqA ax a = true -> 
  (List.filter (λ '(s2, _), eqA ax s2) Y) = 
  (List.filter (λ '(s2, _), eqA s2 a) Y).
Proof.
  induction Y as [|(au, bu) Y IHy].
  +
    cbn; intros; reflexivity.
  +
    cbn; intros * Ha.
    case_eq (eqA ax au);
    case_eq (eqA au a); 
    intros Hb Hc.
    ++
      f_equal.
      exact (IHy _ _ Ha).
    ++
      rewrite (trnA _ _ _ (symA _ _ Hc) Ha) in Hb;
      congruence.
    ++
      rewrite (trnA _ _ _ Ha (symA _ _ Hb)) in Hc;
      congruence.
    ++
      case_eq (eqA au ax);
      intro Hd.
      rewrite (symA _ _ Hd) in Hc;
      congruence.
      exact (IHy _ _ Ha).
Qed.



Lemma filter_argument_swap :
  forall (Y : finite_set (A * P)) a ax, 
  List.filter (λ '(x, _), eqA x a)
    (List.filter (λ '(s2, _), negb (eqA ax s2)) Y) = 
  List.filter (λ '(x, _), eqA a x)
    (List.filter (λ '(s2, _), negb (eqA ax s2)) Y).
Proof.
  intros *.
  rewrite filter_arg_swap_gen with (a := a).
  f_equal.
  apply refA.
Qed.



Lemma fold_right_right : 
  forall (Y : finite_set P) bx, 
  eqP (fold_right addP zeroP
      [fold_right (λ t1 t2 : P, addP t1 t2) bx Y])
  (addP bx (fold_right addP zeroP Y)) = true.
Proof.
  induction Y as [|ay Y IHy].
  +
    intros *.
    cbn; eapply refP.
  +
    intros *.
    cbn.
    specialize (IHy bx).
    eapply trnP with 
      (addP ay (addP bx (fold_right addP zeroP Y))).
    eapply symP.
    eapply trnP with 
      (addP ay (addP (fold_right (λ t1 t2 : P, addP t1 t2) bx Y) zeroP)).
    eapply cong_addP.
    eapply refP.
    eapply symP; exact IHy.
    ++
      eapply symP, addP_assoc.
    ++
      remember ((fold_right addP zeroP Y)) as Ya.
      eapply trnP;
      [eapply addP_com|].
      eapply trnP;
      [eapply addP_assoc|].
      eapply cong_addP.
      eapply refP.
      eapply addP_com.
  Qed.



(* 
  Provable only 
  if we have one (a, p) in Y, 
  i.e., we assume NoDup Y.
  Because here is a counter case: 
  Y := (a, p) :: Y₁ ++ [(a, p)] ++ Y₂
*)
Lemma in_set_fold_left_mmsn_elim_second : 
  forall (X Y : finite_set (A * P))
    (a : A) (p : P),
    no_dup eqA (map fst Y) = true ->
    (* no_dup (brel_product eqA eqP) Y = true -> *)
    (a, p) [in] fold_left [MMSN] X Y ->
    eqP p (sum_fn zeroP addP snd 
      (filter (λ '(x, _), eqA x a) (X ++ Y))) = true.
Proof.
  induction X as [|(ax, bx) X IHx]; simpl.
  +
    intros * Ha Hb.
    destruct (nodup_inset _ _ _ Ha Hb) as 
    (Y₁ & Y₂ & Hc & Hd & He).
    eapply in_list_brel_cong_intro;
    [exact Hc |].
    repeat rewrite <-list_filter_lib_filter_same, 
    filter_app.
    erewrite in_list_filter_empty.
    cbn; rewrite refA; cbn.
    rewrite in_list_filter_empty;
    cbn.
    eapply symP, zeropRid.
    exact He.
    exact Hd.
  +
    intros * Ha Hb.
    case_eq (eqA ax a);
    intro Hc.
    ++
      assert (Hd : no_dup eqA (map fst ([MMSN] Y (ax, bx))) = true).
      eapply no_dup_mmsn; try assumption.
      (* eqA ax a = true *)
      pose proof (IHx ([MMSN] Y (ax, bx)) a p Hd Hb) as He.
      unfold sum_fn in He |- *; cbn.
      repeat rewrite <-list_filter_lib_filter_same, filter_app, map_app in He.
      cbn in He.
      rewrite <-list_filter_lib_filter_same, filter_app in He.
      rewrite filter_argument_swap, filter_empty,
      app_nil_l, fold_left_simp in He.
      cbn in He;
      rewrite Hc in He.
      cbn in He.
      rewrite <-list_filter_lib_filter_same, filter_app, 
      map_app.
      remember (map snd (List.filter (λ '(x, _), eqA x a) X)) as U.
      remember ([fold_left (λ t1 t2 : P, addP t1 t2)
      (map snd (filter (λ '(s2, _), eqA ax s2) Y)) bx]) as V.
      assert (Hf : eqP p (addP (fold_right addP zeroP U) 
      (fold_right addP zeroP V)) = true).
      eapply trnP with (fold_right addP zeroP (U ++ V)); 
      try assumption.
      eapply fold_right_distributes.
      eapply trnP with (addP bx
          (addP 
          (fold_right addP zeroP (map snd (List.filter (λ '(x, _), eqA x a) X))) 
          (fold_right addP zeroP (map snd (List.filter (λ '(x, _), eqA x a) Y))))).

      (* start *)
      assert (Hft : eqP p
      (addP
         (fold_right addP zeroP
            (map snd (List.filter (λ '(x, _), eqA x a) X)))
         (fold_right addP zeroP
            [fold_right (λ t1 t2 : P, addP t1 t2) bx
               (map snd (filter (λ '(s2, _), eqA ax s2) Y))])) = true).
      subst. eapply trnP;
      [eapply Hf |].
      eapply cong_addP;
      [eapply refP|].
      cbn. eapply cong_addP.
      eapply fold_left_right_symmetric; 
      try auto.
      eapply refP.
      clear Hf; rename Hft into Hf.
      (* end *)
      
      (* now replace in He 
      fold_right_right 
      *)
      assert (Hg : 
      eqP p
      (addP
        (fold_right addP zeroP
            (map snd (List.filter (λ '(x, _), eqA x a) X)))
        (addP bx (fold_right addP zeroP 
          (map snd (filter (λ '(s2, _), eqA ax s2) Y))))) = true).
      eapply trnP.
      exact Hf.
      eapply cong_addP.
      eapply refP.
      eapply fold_right_right.
      (* I am close *)
      remember 
      ((fold_right addP zeroP
      (map snd (List.filter (λ '(x, _), eqA x a) X)))) as Xv.
      rewrite <-list_filter_lib_filter_same in Hg.
      rewrite filter_arg_swap_gen with (a := a) in Hg.
      remember ((fold_right addP zeroP
      (map snd (List.filter (λ '(s2, _), eqA s2 a) Y)))) as Yv.
      (* start *)
      eapply trnP;
      [eapply Hg | ].
      eapply trnP;
      [eapply addP_com|].
      eapply trnP with (addP bx (addP Yv Xv));
      [eapply addP_assoc | eapply cong_addP].
      eapply refP. eapply addP_com.
      exact Hc.
      eapply cong_addP.
      eapply refP.
      eapply symP.
      subst.
      eapply fold_right_distributes.
      exact Hc.
      (* end *)
    ++
      (* eqA ax a = false *)
      (* 
      (a, p) [in] fold_left [MMSN] X ([MMSN] Y (ax, bx)) = 
      (a, p) [in] fold_left [MMSN] X Y 
      eapply Inductive Hypothesis and 
      we are home 
      *)
      rewrite in_set_equality_false in Hb;
      try assumption.
      eapply IHx; try assumption.
      case_eq (eqA a ax);
      intros Hd.
      rewrite (symA _ _ Hd) in Hc;
      congruence.
      reflexivity.
Qed.



Lemma in_set_fold_left_mmsn_elim : 
  forall (X Y : finite_set (A * P))
    (a : A) (p : P),
    no_dup eqA (map fst Y) = true  ->
    (a, p) [in] fold_left [MMSN] X Y ->
    (∃ q : P, (a, q) [in] (X ++ Y)) ∧ 
    eqP p (sum_fn zeroP addP snd 
      (filter (λ '(x, _), eqA x a) (X ++ Y))) = true.
Proof.
  intros * Ha Hb.
  split;
  [eapply in_set_fold_left_mmsn_elim_first |
  eapply in_set_fold_left_mmsn_elim_second];
  try assumption; exact Hb.
Qed.


Lemma in_set_uop_manger_phase_1_elim : 
  forall (X : finite_set (A * P)) 
  (a : A) (p : P),
  in_set  (brel_product eqA eqP) 
    (uop_manger_phase_1 eqA addP X) (a, p) = true ->
  (∃ q : P, (a, q) [in] X) ∧ 
  eqP p (sum_fn zeroP addP snd 
    (filter (λ '(x, _), eqA x a) X)) = true.
Proof.
    intros ? ? ? Ha.
    unfold uop_manger_phase_1,
    manger_phase_1_auxiliary in Ha;
    rewrite manger_merge_set_funex in Ha.
    (*
      generalise the [] to Y because it will 
      make the induction hypothesis stronger, 
      otherwise it is impossible to prove this, 
      at least from my experience.
    *)
    replace (X) with (X ++ []).
    eapply in_set_fold_left_mmsn_elim with (Y := nil).
    +
      constructor.
    +
      exact Ha.
    +
      rewrite app_nil_r;
      exact eq_refl.
Qed.


Lemma in_set_uop_manger_phase_2_intro : 
  forall (X : finite_set (A * P)) 
  (a : A) (p : P),
  (a, p) [in] X ->
  (forall (b : A) (q : P), (b, q) [in] X -> 
    below lteA a b = false) ->  
  in_set (brel_product eqA eqP) 
    (uop_manger_phase_2 lteA X) (a, p) = true.
Proof.
  intros ? ? ? Ha Hb.
  apply in_minset_intro;
  [eapply refAP |
  eapply symAP |
  eapply manger_pre_order_congruence |
  eapply manger_pre_order_reflexive |].
  split.
  + 
    exact Ha.
  +
    intros (tx, ty) Hc.
    apply below_false_intro.
    pose proof (Hb _ _ Ha) as Hd.
    pose proof (Hb _ _ Hc) as He.
    eapply below_false_elim in He.
    destruct He as [He | He];
    compute; rewrite He; auto.
  Qed.

 
  

Lemma in_set_uop_manger_phase_2_elim : 
  forall (X : finite_set (A * P)) 
  (a : A) (p : P),  
  in_set (brel_product eqA eqP) 
    (uop_manger_phase_2 lteA X) (a, p) = true ->
  (a, p) [in] X ∧
  (forall (b : A) (q : P), (b, q) [in] X -> 
    below lteA a b = false).
Proof.
  intros ? ? ? Ha.
  eapply in_minset_elim in Ha.
  destruct Ha as [Hal Har].
  refine(conj _ _);
  [exact Hal |].
  intros ? ? Hb.
  pose proof (Har _ Hb) as Hc.
  compute in Hc.
  compute.
  case_eq (lteA b a);
  intros Hd.
  rewrite Hd in Hc.
  case_eq (lteA a b);
  intros He.
  reflexivity.
  rewrite He in Hc;
  congruence.
  reflexivity.
  apply refAP.
  apply symAP.
  eapply manger_pre_order_congruence.
  eapply manger_pre_order_reflexive.
  eapply manger_pre_order_transitive.
Qed.



End Theory.   
