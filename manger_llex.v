Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.trivial.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.reduce.
Require Import CAS.coq.eqv.minset. 
Require Import CAS.coq.eqv.manger_sets.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.reduce.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.minset_union.

Require Import CAS.coq.theory.set.
Require Import CAS.coq.uop.properties. 
Require Import CAS.coq.uop.commutative_composition. 
Import ListNotations.
(* 
  A = type of active component
  P = type of passive component

  See cas/coq/uop/commutative_composition.v 
  for a description of the composition 
  of two reductions, r1 and 2, that 
  commute: 
     r1 (r1 s) = r1 (r2 s). 

  I believe this is the case for our manger reductions: 

   r1 = uop_manger_phase_1

   r2 = uop_manger_phase_2 

   both considered as reductions over 

   b = bop_union (brel_product eqA eqP). 

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
    (refA : brel_reflexive A eqA)
    (symA : brel_symmetric A eqA)
    (trnA : brel_transitive A eqA)
    (conP : brel_congruence P eqP eqP)
    (cong_addP : bop_congruence P eqP addP) 
    (refP : brel_reflexive P eqP)
    (symP : brel_symmetric P eqP)
    (trnP : brel_transitive P eqP)
    (conLte : brel_congruence A eqA lteA) 
    (refLte : brel_reflexive A lteA)
    (trnLte : brel_transitive A lteA) 
    (ntot : brel_not_total A lteA)
    (addP_assoc : bop_associative P eqP addP)
    (addP_com : bop_commutative P eqP addP)
    (* idempotence is baked in this addP_gen_idempotent but it can be proved *)
    (zeropLid : ∀ (p : P), eqP (addP zeroP p) p = true)
    (zeropRid : ∀ (p : P), eqP (addP p zeroP) p = true)
    (addP_gen_idempotent : ∀ x y : P, eqP x y = true → eqP (addP x y) y = true).
    
  Local Definition eqAP : brel (A * P)
    := brel_product eqA eqP.
  
  Local Definition eqSAP : brel (finite_set (A * P))
    := brel_set eqAP.
  
  Local Definition bSAP : binary_op (finite_set (A * P))
    := bop_union eqAP.

  Lemma conAP : brel_congruence (A * P) eqAP eqAP.
  Proof. apply brel_product_congruence; auto. Qed. 

  Lemma refAP : brel_reflexive (A * P) eqAP.
  Proof. apply brel_product_reflexive; auto. Qed. 

  Lemma symAP : brel_symmetric (A * P) eqAP.
  Proof. apply brel_product_symmetric; auto. Qed. 

  Lemma trnAP : brel_transitive (A * P) eqAP.
  Proof. apply brel_product_transitive; auto. Qed. 

  Lemma conSAP : brel_congruence (finite_set (A * P)) eqSAP eqSAP.
  Proof. apply brel_set_congruence.
         - apply refAP. 
         - apply symAP.
         - apply trnAP.
  Qed. 


  Lemma refSAP : brel_reflexive (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_reflexive. 
         - apply refAP. 
         - apply symAP. 
  Qed. 

  Lemma symSAP : brel_symmetric (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_symmetric. Qed. 

  Lemma trnSAP : brel_transitive (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_transitive. 
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_cong : bop_congruence _ eqSAP bSAP.
  Proof. apply bop_union_congruence.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_associative : bop_associative _ eqSAP bSAP.
  Proof. apply bop_union_associative.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_commutative : bop_commutative _ eqSAP bSAP.
   Proof. apply bop_union_commutative.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_idempotent : bop_idempotent _ eqSAP bSAP.
  Proof. apply bop_union_idempotent.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed.

  (*  Ha! this is interesting. 
      The witness from sg.union.bop_union_not_selective for our type eqAP is (X, Y), where 
      X =  (wA, wP) ::nil 
      Y =  (fA wA, wP) ::nil
      where 
      Variable fA : A -> A. 
      Variable ntA brel_not_trivial A eqA fA.

      Ouch!  This does not work for Lemma nsel_witness_is_a_reduction_witness below. 
    
      That lemma needs 

        uop_manger { (wA, wP), (fA wA, wP)} not in { { (wA, wP) }, { (fA wA, wP)}}

      BUT, wA <> fA wA, so the minset of P2 will choose one of them!!! Ouch! 

    Solution?  It seems we need to come up with a bespoke proof of bSAP_not_selective
    just for this file, so that the witness makes this Lemma true. 
    But the witness has to be simple enough so that 
    we can prove fst_nsel_witness_is_fixed_point and snd_nsel_witness_is_fixed_point. 
    So, we need X and Y such that 

    1) uop_manger X = X
    2) uop_manger Y = Y
    3) uop_manger (X union Y) not in {X, Y}. 

    This can be done.  Here's how. 
    The whole scheme of manger only makes sence when lteA is a partial order. 
    So, let (a1, a2) be the witness for (ntot : brel_not_total A lteA), 
    then 
    X = {
    Y = {(a2, wP)} 
    will work since 
    uop_manger {(a1, wP), (a2, wP)} = {(a1, wP), (a2, wP)}. 

    Here is the bespoke proof of lack of selectivity for union: 
   *)
  Lemma bSAP_not_selective : bop_not_selective _ eqSAP bSAP.
  Proof. destruct ntot as [[a1 a2] [L R]].
         exists ((a1, wP)::nil, (a2, wP)::nil). split.
         - case_eq(eqSAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) ((a1, wP) :: nil)); intro H1; auto.
           apply brel_set_elim_prop in H1.
           destruct H1 as [H1 H2].
           assert (H3 : in_set eqAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) (a2, wP) = true).
           {
             apply in_set_bop_union_intro.
             + apply symAP.
             + apply trnAP.
             + right. apply in_set_cons_intro.
               * apply symAP.
               * left. apply refAP. 
           }
           assert (H4 := H1 _ H3).
           apply in_set_cons_elim in H4.
           + destruct H4 as [H4 | H4].
             * apply brel_product_elim in H4. destruct H4 as [H4 H5].
               assert (H6 := refLte a1).
               assert (H7 := conLte _ _ _ _ (refA a1) H4).
               rewrite H7 in H6. rewrite H6 in L.
               exact L. 
             * compute in H4.
               discriminate H4.
           + apply symAP.
           + apply symAP.
           + apply trnAP.
         - case_eq(eqSAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) ((a2, wP) :: nil)); intro H1; auto.
           apply brel_set_elim_prop in H1.
           destruct H1 as [H1 H2].
           assert (H3 : in_set eqAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) (a1, wP) = true).
           {
             apply in_set_bop_union_intro.
             + apply symAP.
             + apply trnAP.
             + left. apply in_set_cons_intro.
               * apply symAP.
               * left. apply refAP. 
           }
           assert (H4 := H1 _ H3).
           apply in_set_cons_elim in H4.
           + destruct H4 as [H4 | H4].
             * apply brel_product_elim in H4. destruct H4 as [H4 H5].
               assert (H6 := refLte a1).
               assert (H7 := conLte _ _ _ _ (refA a1) H4).
               rewrite H6 in H7. rewrite H7 in L.
               exact L. 
             * compute in H4.
               discriminate H4.
           + apply symAP.
           + apply symAP.
           + apply trnAP.
  Defined. 

  Local Notation "x =S= y" := (eqSAP x y = true) (at level 70,
  only parsing).
  Local Notation "[P1]" := (uop_manger_phase_1 eqA addP)
    (only parsing).  (* Phase 1 reduction *) 
  Local Notation "[P2]" := (@uop_manger_phase_2 A P lteA)
    (only parsing). (* Phase 2 reduction *)



  (* These admitted lemmas will come from Matrix.algorithm because 
    Tim is working on it, so for the moment I am admitting it. *)

  Lemma sum_fn_congruence_general_set :
    forall (Xa Xb : finite_set (A * P)),
    Xa =S= Xb ->
    eqP (matrix_algorithms.sum_fn zeroP addP snd Xa)
    (matrix_algorithms.sum_fn zeroP addP snd Xb) = true.
  Proof.
  Admitted.

  

  (* End of admit that will come from library *)


   (* Move these lemmas to respective files *)

  Lemma sum_fn_distribute : 
    forall (X Y : finite_set (A * P)),
    eqP 
    (matrix_algorithms.sum_fn zeroP addP snd (X ++ Y))
    (addP 
      (matrix_algorithms.sum_fn zeroP addP snd X)
    (matrix_algorithms.sum_fn zeroP addP snd Y)) = true.
  Proof.
    intros *.
    eapply matrix_algorithms.sum_fn_distributes_over_concat;
    auto.
    unfold bop_is_id; split;
    [eapply zeropLid | eapply zeropRid].
  Qed.
    
   
  Lemma sum_fn_commutative : 
    forall (X Y : finite_set (A * P)),
    eqP 
    (matrix_algorithms.sum_fn zeroP addP snd (X ++ Y))
    (matrix_algorithms.sum_fn zeroP addP snd (Y ++ X)) = true.
  Proof.
    intros *.
    eapply trnP;
    [eapply sum_fn_distribute |].
    eapply symP, trnP;
    [eapply sum_fn_distribute|].
    eapply trnP;
    [eapply addP_com| eapply refP].
  Qed.

  Lemma sum_fn_base_case : 
    forall (Y : finite_set (A * P)), 
    eqP 
    (fold_right addP zeroP (map snd (uop_duplicate_elim eqAP Y)))
    (addP zeroP (fold_right addP zeroP (map snd Y))) = true.
  Proof.
    induction Y as [|(au, bu) Y IHy].
    +
      cbn; eapply symP.
      rewrite zeropRid;
      exact eq_refl.
    +
      cbn;
      case_eq (in_set eqAP Y (au, bu));
      intros Ha.
      ++
        eapply symP, trnP with 
        (addP zeroP (fold_right addP zeroP (map snd Y))).
        remember ((map snd Y)) as Ya.
        eapply trnP with 
        (addP bu (fold_right addP zeroP Ya));
        [eapply zeropLid | eapply symP].
        eapply trnP with 
        (fold_right addP zeroP Ya);
        [eapply zeropLid|].
        eapply symP.
        eapply fold_right_idempotent_aux_one; 
        try assumption.
        intros *;
        eapply symP, addP_assoc.
        intros * Hu Hv;
        eapply cong_addP; try assumption.
        eapply map_in_set with (au := au) (bu := bu) in Ha; 
        try assumption.
        destruct Ha as (Hal & Har).
        subst; exact Har.
        now rewrite refA.
        now rewrite refP.
        eapply symP, IHy.
      ++
        cbn; eapply symP, trnP with
        (addP bu (fold_right addP zeroP (map snd Y))).
        eapply zeropLid.
        eapply cong_addP;
        [now rewrite refP|].
        eapply symP, trnP. 
        eapply IHy. 
        eapply zeropLid.
  Qed.
       

  (* Easy. This proof certainly needs idempontence because of duplicate
    elimination during bop_union *)
  Lemma sum_fn_bop_union_dist : 
    forall (X Y : finite_set (A * P)),
    eqP
    (matrix_algorithms.sum_fn zeroP addP snd (bop_union eqAP X Y))
    (addP 
      (matrix_algorithms.sum_fn zeroP addP snd X)
      (matrix_algorithms.sum_fn zeroP addP snd Y)) = true.
  Proof.
    induction X as [|(ax, bx) X IHx].
    + 
      intros *; cbn;
      unfold matrix_algorithms.sum_fn.
      eapply sum_fn_base_case.
    +
      intros *; cbn.
      case_eq (in_set eqAP (X ++ Y) (ax, bx));
      intro Ha.
      ++
        (* idempotence *)
        specialize (IHx Y).
        unfold matrix_algorithms.sum_fn, bop_union,
        bop_concat in * |- *.
        eapply trnP;
        [eapply IHx|].
        eapply trnP.
        eapply symP, fold_right_distributes;
        try assumption.
        eapply symP, trnP.
        eapply addP_assoc.
        eapply trnP with 
          (addP bx (fold_right addP zeroP (map snd X ++ map snd Y))),
        symP.
        eapply cong_addP;
        [eapply refP|].
        eapply symP, fold_right_distributes;
        try assumption.
        eapply symP, fold_right_idempotent_aux_one; 
        try assumption.
        intros *;
        eapply symP, addP_assoc.
        intros * Hu Hv;
        eapply cong_addP; try assumption.
        eapply map_in_set with (au := ax) (bu := bx) in Ha;
        try assumption.
        destruct Ha as (Hal & Har).
        rewrite map_app in Har; exact Har.
        now rewrite refA.
        now rewrite refP.
      ++
        cbn;
        unfold matrix_algorithms.sum_fn, bop_union,
        bop_concat in * |- *.
        eapply symP, trnP.
        eapply addP_assoc.
        eapply cong_addP;
        [now rewrite refP| eapply symP, IHx].
  Qed.


 

  Lemma in_set_filter : 
    forall (X : finite_set (A * P)) ap ax bx, 
    eqA ax ap = true -> 
    in_set eqAP X (ax, bx) = true ->
    in_set eqAP (filter (λ '(x, _), eqA x ap) X) (ax, bx) = true.
  Proof.
    induction X as [|(au, bu) X IHx].
    +
      cbn; intros; 
      try congruence.
    +
      cbn; intros * Ha Hb.
      case_eq (and.bop_and (eqA ax au) (eqP bx bu));
      intro Hc; rewrite Hc in Hb; cbn in Hb.
      ++
        eapply Bool.andb_true_iff in Hc.
        destruct Hc as [Hcl Hcr].
        case_eq (eqA au ap); intro Hd.
        cbn; rewrite Hcl, Hcr; 
        reflexivity.
        rewrite (trnA _ _ _ (symA _ _ Hcl) Ha) in Hd;
        congruence.
      ++
        case_eq (eqA au ap); intro Hd.
        cbn; rewrite (trnA _ _ _ Ha (symA _ _ Hd)) in Hc |- *;
        cbn in Hc |- *; rewrite Hc; cbn.
        eapply IHx; try assumption.
        eapply IHx; try assumption.
  Qed.





  Lemma uop_dup_dup_elim : 
    forall (X : finite_set (A * P)) ax bx, 
    in_set eqAP X (ax, bx) = true ->
    uop_duplicate_elim eqAP ((ax, bx) :: X) = 
    uop_duplicate_elim eqAP X.
  Proof.
    intros * Ha.
    cbn; rewrite Ha;
    reflexivity.
  Qed.
  
  
  Lemma uop_dup_filter_elim : 
    forall (X : finite_set (A * P)) ap, 
    uop_duplicate_elim eqAP (filter (λ '(x, _), eqA x ap) X) =
    filter (λ '(x, _), eqA x ap) (uop_duplicate_elim eqAP X).
  Proof.
    induction X as [|(ax, bx) X IHx].
    +
      intros *; cbn;
      exact eq_refl.
    +
      intros *; cbn.
      case_eq (eqA ax ap);
      case_eq (in_set eqAP X (ax, bx));
      intros Ha Hb.
      ++
         (* we know that (ax, bx) is a
         member of filter *)
        rewrite <-IHx.
        pose proof in_set_filter X ap ax bx Hb
          Ha as Hc.
        rewrite uop_dup_dup_elim;
        [exact eq_refl | exact Hc].
      ++
        rewrite uop_duplicate_elim_lemma_2;
        cbn. rewrite Hb, IHx;
        reflexivity.
        case_eq (in_set eqAP (filter (λ '(x, _), eqA x ap) X) (ax, bx));
        intro Hc; try reflexivity.
        eapply in_set_filter_elim in Hc;
        [rewrite Ha in Hc; destruct Hc; congruence|].
        intros (au, bu) (cu, du) He.
        eapply brel_product_elim in He.
        destruct He as (Hel & Her).
        eapply conA; try assumption.
        now rewrite refA.
      ++
        eapply IHx.
      ++
        cbn; rewrite Hb;
        eapply IHx.
  Qed.
        


  Lemma bop_union_filter_push : 
    forall (X Y : finite_set (A * P)) ap,
    bop_union eqAP 
      (filter (λ '(x, _), eqA x ap) X)
      (filter (λ '(x, _), eqA x ap) Y) = 
    filter (λ '(x, _), eqA x ap) (bop_union eqAP X Y).
  Proof.
    induction X as [|(ax, bx) X IHx].
    +
      intros *; cbn.
      eapply uop_dup_filter_elim.
    +
      intros *; cbn.
      case_eq (eqA ax ap);
      case_eq (in_set eqAP (X ++ Y) (ax, bx));
      intros Ha Hb.
      ++
        remember (filter (λ '(x, _), eqA x ap) X) as Xa.
        remember (filter (λ '(x, _), eqA x ap) Y) as Ya.
        rewrite <-app_comm_cons, uop_dup_dup_elim; subst;
        [eapply IHx |].
        repeat rewrite <-list_filter_lib_filter_same;
        rewrite <-filter_app, list_filter_lib_filter_same.
        eapply in_set_filter_intro;
        [eapply symAP| | refine(pair Hb Ha)].
        intros (au, bu) (cu, du) He.
        eapply brel_product_elim in He.
        destruct He as (Hel & Her).
        eapply conA; try assumption.
        now rewrite refA.
      ++
        remember (filter (λ '(x, _), eqA x ap) X) as Xa.
        remember (filter (λ '(x, _), eqA x ap) Y) as Ya.
        rewrite <-app_comm_cons, uop_duplicate_elim_lemma_2;
        cbn. rewrite Hb. f_equal.
        subst; eapply IHx.
        subst.
        repeat rewrite <-list_filter_lib_filter_same.
        rewrite <-filter_app, list_filter_lib_filter_same.
        case_eq (in_set eqAP (filter (λ '(x, _), eqA x ap) (X ++ Y)) (ax, bx));
        intro Hc; try reflexivity.
        eapply in_set_filter_elim in Hc;
        [rewrite Ha in Hc; destruct Hc; congruence|].
        intros (au, bu) (cu, du) He.
        eapply brel_product_elim in He.
        destruct He as (Hel & Her).
        eapply conA; try assumption.
        now rewrite refA.
      ++
        eapply IHx.
      ++
        cbn; rewrite Hb.
        eapply IHx.
  Qed.

  (* end of lemma movement *)
  Lemma matrix_sum_filter_push_inside :
    forall (X Y : finite_set (A * P)) au bu ap, 
    eqA au ap = true ->
    eqP 
    (matrix_algorithms.sum_fn zeroP addP snd
      ((au, bu) :: filter (λ '(x, _), eqA x ap) (X ++ Y)))
    (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x ap) (X ++ ((au, bu) :: Y)))) = true.
  Proof.
    intros * Ha.
    repeat rewrite <-list_filter_lib_filter_same;
    repeat rewrite filter_app; cbn;
    rewrite Ha; cbn.
    remember (List.filter (λ '(x, _), eqA x ap) X) as Xa.
    remember ((au, bu) :: List.filter (λ '(x, _), eqA x ap) Y) 
    as Ya.
    eapply symP, trnP;
    [eapply sum_fn_commutative |].
    subst; cbn.
    eapply cong_addP;
    [eapply refP |].
    eapply sum_fn_commutative.
  Qed.


  Lemma matrix_sum_fn_addition : 
    forall (X Y : finite_set (A * P)) ap,
    no_dup eqA (map fst Y) = true ->
    eqP
    (matrix_algorithms.sum_fn zeroP addP snd
     (filter (λ '(x, _), eqA x ap) (X ++ Y)))
    (matrix_algorithms.sum_fn zeroP addP snd
     (filter (λ '(x, _), eqA x ap)
      (fold_left (manger_merge_sets_new eqA addP) X Y))) = true.
  Proof.
    induction X as [|(au, bu) X IHx].
    + intros * Ha. cbn. 
      eapply refP.
    +
      simpl; intros * Ha.
      unfold manger_merge_sets_new at 2;
      unfold manger_merge_sets_new_aux;
      cbn.
      remember (filter (λ '(s2, _), negb (eqA au s2)) Y) as Ya;
      destruct (fold_left
      (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
      (filter (λ '(s2, _), eqA au s2) Y) (au, bu)) 
      as (aw, av) eqn:Hb;
      rewrite fold_left_simp in Hb;
      inversion Hb; clear Hb;
      rename H0 into Hb;
      rename H1 into Hc;
      rewrite Hc, <-Hb;
      assert (Hd : no_dup eqA (map fst (Ya ++ [(au, av)])) = true).
      rewrite map_app; cbn; subst.
      eapply no_dup_filter; auto.
      (* Y is duplicate free *)
      rewrite <-Hb in Hc.
      specialize (IHx (Ya ++ [(au, av)]) ap Hd).
      eapply symP in IHx. 
      eapply symP.
      eapply trnP; 
      [eapply IHx |].
      (* This one is bit easy goal! Thanks Tim for 
      the idea! *)
      case_eq (eqA au ap);
      intro He.
      ++
        eapply symP, trnP;
        [eapply matrix_sum_filter_push_inside; 
        exact He|].
        repeat rewrite <-list_filter_lib_filter_same, 
        filter_app;
        repeat rewrite list_filter_lib_filter_same.
        eapply trnP;
        [eapply sum_fn_distribute |].
        eapply symP, trnP;
        [eapply sum_fn_distribute |].
        eapply cong_addP;
        [eapply refP|].
        rewrite HeqYa.
        (* requires some thinking! *)
        repeat rewrite <-list_filter_lib_filter_same, 
        filter_app.
        repeat rewrite <-list_filter_lib_filter_same.
        (* why rewriting is such a mess! *)
        rewrite <-filter_arg_swap_gen  
        with (ax := ap) at 1; auto.
        rewrite filter_empty; auto.
        cbn; rewrite He; cbn.
        rewrite <-Hc.
        (* start *)
        eapply trnP with 
        (addP
        (fold_right (λ t1 t2 : P, addP t1 t2) bu
          (map snd (filter (λ '(s2, _), eqA au s2) Y))) zeroP).
        remember ((map snd (filter (λ '(s2, _), eqA au s2) Y))) as Yt.
        eapply trnP;
        [eapply zeropRid| eapply symP].
        eapply trnP;
        [eapply zeropRid | eapply symP].
        eapply list_congruences.fold_symmetric_with_equality;
        try auto.
        (* end *)
        eapply trnP with 
        ((fold_right (λ t1 t2 : P, addP t1 t2) bu
        (map snd (filter (λ '(s2, _), eqA au s2) Y)))).
        eapply zeropRid.
        eapply trnP;
        [eapply fold_right_zero |]; auto.
        eapply cong_addP;
        [eapply refP|].
        repeat rewrite <-list_filter_lib_filter_same.
        rewrite <-filter_arg_swap_gen  
        with (ax := ap) at 1; auto.
        repeat rewrite list_filter_lib_filter_same.
        erewrite filter_equality with (a := au); auto.
      
      ++
        repeat rewrite <-list_filter_lib_filter_same;
        repeat rewrite filter_app;
        repeat rewrite list_filter_lib_filter_same.
        eapply trnP;
        [eapply sum_fn_distribute |].
        eapply symP, trnP;
        [eapply sum_fn_distribute |].
        eapply cong_addP;
        [eapply refP|].
        cbn; rewrite He, app_nil_r.
        rewrite HeqYa.
        (* requires some thinking! *)
        repeat rewrite <-list_filter_lib_filter_same.
        eapply symP.
        rewrite <-filter_arg_swap_gen  
        with (ax := ap) at 1; auto.
        rewrite filter_filter; auto.
        rewrite <-filter_arg_swap_gen  
        with (ax := ap) at 1; auto.
        case_eq (eqA ap au);
        intro Hf; try reflexivity.
        rewrite (symA _ _ Hf) in He;
        congruence.
  Qed.
      

  Lemma sum_fn_cong_bop_union_X : 
    forall (X Y : finite_set (A * P)) ap, 
    eqP
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap)
        (bop_union eqAP 
          (fold_left (manger_merge_sets_new eqA addP) X []) Y)))
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) (bop_union eqAP X Y))) = true.
  Proof.
    intros *;
    repeat rewrite <-bop_union_filter_push.
    remember ((filter (λ '(x, _), eqA x ap) Y)) as Ya.
    remember ((filter (λ '(x, _), eqA x ap)
    (fold_left (manger_merge_sets_new eqA addP) X []))) as Xa.
    remember ((filter (λ '(x, _), eqA x ap) X)) as Xb.
    eapply trnP;
    [eapply sum_fn_bop_union_dist |].
    eapply symP, trnP;
    [eapply sum_fn_bop_union_dist |].
    eapply cong_addP;
    [| now rewrite refP].
    subst.
    replace (X) with (X ++ []) at 1.
    now erewrite matrix_sum_fn_addition.
    now rewrite app_nil_r.
  Qed.

    


  Lemma sum_fn_cong_bop_union_Y : 
    forall (X Y : finite_set (A * P)) ap, 
    eqP
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap)
        (bop_union eqAP X 
          (fold_left (manger_merge_sets_new eqA addP) Y []))))
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) (bop_union eqAP X Y))) = true.
  Proof.
    intros *.
    repeat rewrite <-bop_union_filter_push.
    remember ((filter (λ '(x, _), eqA x ap) X)) as Xa.
    remember (filter (λ '(x, _), eqA x ap)
           (fold_left (manger_merge_sets_new eqA addP) Y [])) as Ya.
    remember ((filter (λ '(x, _), eqA x ap) Y)) as Yb.
    eapply trnP;
    [eapply sum_fn_bop_union_dist |].
    eapply symP, trnP;
    [eapply sum_fn_bop_union_dist |].
    eapply cong_addP;
    [now rewrite refP|].
    subst.
    replace (Y) with (Y ++ []) at 1.
    now erewrite matrix_sum_fn_addition.
    now rewrite app_nil_r.
  Qed.



  Lemma bop_congruence_bProp_fst : 
    forall (a : A),
    theory.bProp_congruence (A * P) (brel_product eqA eqP)
    (λ '(x, _), eqA x a).
  Proof.
    intros a.
    unfold theory.bProp_congruence.
    intros (aa, ap) (ba, bp) He.
    apply brel_product_elim in He.
    destruct He as [Hel Her].
    case_eq (eqA aa a); intro Hf.
    eapply symA in Hel.
    rewrite (trnA _ _ _  Hel Hf);
    reflexivity.
    case_eq (eqA ba a); intro Hg.
    rewrite (trnA _ _ _ Hel Hg) in Hf;
    congruence.
    reflexivity.
  Qed.

  Lemma bop_congruence_bProp_snd : 
    forall (pa : A),theory.bProp_congruence _  
    (brel_product eqA eqP)
    (λ '(s2, _), eqA pa s2).
  Proof.
    intros pa (aa, ap) (ba, bp) He.
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


  (* show [P1] is a reduction *)  
  Lemma P1_cong : uop_congruence _ eqSAP [P1].
  Proof.
    intros X Y Ha.
    eapply brel_set_intro_prop;
    [exact refAP| refine(pair _ _); intros (ap, bp) Hb].
    + 
      unfold uop_manger_phase_1, 
      manger_phase_1_auxiliary in Hb |- *;
      rewrite manger_merge_set_funex in Hb |- *.
      eapply in_set_fold_left_mmsn_intro with 
      (zeroP := zeroP); try assumption.
      ++
        eapply in_set_fold_left_mmsn_elim with 
        (zeroP := zeroP) in Hb; try assumption.
        destruct Hb as [(q & Hbl) Hbr].
        eapply brel_set_elim_prop in Ha;
        [|exact symAP | eapply trnAP].
        destruct Ha as [Hal Har].
        exists q; eapply Hal;
        rewrite app_nil_r in Hbl;
        exact Hbl.
        cbn; reflexivity.
      ++
        eapply in_set_fold_left_mmsn_elim with 
        (zeroP := zeroP) in Hb; cbn; try assumption;
        try reflexivity.
        destruct Hb as [Hbl Hbr].
        rewrite app_nil_r in Hbr |- *.
        rewrite <-list_filter_lib_filter_same,
        filter_arg_swap_gen with (a := ap), 
        list_filter_lib_filter_same; try assumption;
        try (apply refA).
        assert (Hc : (filter (λ '(x, _), eqA x ap) X) =S= 
        (filter (λ '(x, _), eqA x ap) Y)).
        eapply filter_congruence_gen; try assumption;
        try (apply bop_congruence_bProp_fst).
        eapply symP, trnP.
        eapply sum_fn_congruence_general_set,
        brel_set_symmetric; exact Hc.
        eapply symP; exact Hbr.
    +
      unfold uop_manger_phase_1, 
      manger_phase_1_auxiliary in Hb |- *;
      rewrite manger_merge_set_funex in Hb |- *.
      eapply in_set_fold_left_mmsn_intro with 
      (zeroP := zeroP); try assumption.
      ++
        eapply in_set_fold_left_mmsn_elim with 
        (zeroP := zeroP) in Hb; try assumption.
        destruct Hb as [(q & Hbl) Hbr].
        eapply brel_set_elim_prop in Ha;
        [|exact symAP | eapply trnAP].
        destruct Ha as [Hal Har].
        exists q; eapply Har;
        rewrite app_nil_r in Hbl;
        exact Hbl.
        cbn; reflexivity.
      ++
        eapply in_set_fold_left_mmsn_elim with 
        (zeroP := zeroP) in Hb; cbn; try assumption;
        try reflexivity.
        destruct Hb as [Hbl Hbr].
        rewrite app_nil_r in Hbr |- *.
        rewrite <-list_filter_lib_filter_same,
        filter_arg_swap_gen with (a := ap), 
        list_filter_lib_filter_same; try assumption;
        try (apply refA).
        assert (Hc : (filter (λ '(x, _), eqA x ap) X) =S= 
        (filter (λ '(x, _), eqA x ap) Y)).
        eapply filter_congruence_gen; try assumption;
        try (apply bop_congruence_bProp_fst).
        eapply symP, trnP.
        eapply sum_fn_congruence_general_set;
        exact Hc.
        eapply symP; exact Hbr.
  Qed.

        

  
  Lemma P1_idem : uop_idempotent _ eqSAP [P1].
  Proof.
    eapply uop_manger_phase_1_uop_idempotent;
    try assumption.
    unfold bop_idempotent;
    intros.
    eapply addP_gen_idempotent;
    now rewrite refP.
  Qed.
  
  


  Lemma P1_left : bop_left_uop_invariant _ 
    eqSAP (bop_reduce [P1] bSAP) [P1].
  Proof.
    intros X Y;
    eapply brel_set_intro_prop;
    [exact refAP| refine(pair _ _); intros (ap, bp) Ha].
    +
      unfold bop_reduce in Ha |- *.
      eapply in_set_uop_manger_phase_1_elim in Ha; 
      auto.
      destruct Ha as ((q & Hal) & Har).
      unfold bSAP in Hal.
      eapply in_set_bop_union_elim in Hal; 
      [|eapply symAP].
      eapply in_set_uop_manger_phase_1_intro;
      auto.
      ++
        destruct Hal as [Hall | Halr].
        +++
          eapply in_set_uop_manger_phase_1_elim in Hall;
          auto.
          destruct Hall as ((q' & Halll) & Hallr).
          exists q'.
          eapply in_set_bop_union_intro;
          [eapply symAP | eapply trnAP | ].
          left; exact Halll.
        +++
          exists q.
          eapply in_set_bop_union_intro;
          [eapply symAP | eapply trnAP | ].
          right; exact Halr.
      ++
        unfold uop_manger_phase_1, 
        manger_phase_1_auxiliary in Har |- *;
        rewrite manger_merge_set_funex in Har.
        eapply trnP;[exact Har |
        rewrite list_filter_lib_filter_same;
        eapply sum_fn_cong_bop_union_X].
    +
      unfold bop_reduce in Ha |- *.
      eapply in_set_uop_manger_phase_1_elim in Ha; 
      auto.
      destruct Ha as ((q & Hal) & Har).
      unfold bSAP in Hal.
      eapply in_set_bop_union_elim in Hal; 
      [|eapply symAP].
      eapply in_set_uop_manger_phase_1_intro;
      auto.
      ++
        destruct Hal as [Hall | Halr].
        +++
          eexists.
          eapply in_set_bop_union_intro;
          [apply symAP | eapply trnAP|].
          left;
          eapply in_set_uop_manger_phase_1_intro; auto;
          exists q; exact Hall.
        +++
          exists q.
          eapply in_set_bop_union_intro;
          [eapply symAP | eapply trnAP | ].
          right; exact Halr.
      ++
        unfold uop_manger_phase_1, 
        manger_phase_1_auxiliary in *;
        rewrite manger_merge_set_funex in *.
        eapply trnP;[exact Har |
        rewrite list_filter_lib_filter_same;
        eapply symP, sum_fn_cong_bop_union_X].
  Qed.

      

  
  Lemma P1_right : bop_right_uop_invariant _ eqSAP (bop_reduce [P1] bSAP) [P1].
  Proof.
    intros X Y.
    eapply brel_set_intro_prop;
    [exact refAP| refine(pair _ _); intros (ap, bp) Ha].
    +
      unfold bop_reduce in Ha |- *.
      eapply in_set_uop_manger_phase_1_elim in Ha; 
      auto.
      destruct Ha as ((q & Hal) & Har).
      unfold bSAP in Hal.
      eapply in_set_bop_union_elim in Hal; 
      [|eapply symAP].
      eapply in_set_uop_manger_phase_1_intro;
      auto.
      ++
        destruct Hal as [Hall | Halr].
        +++
          exists q.
          eapply in_set_bop_union_intro;
          [apply symAP | eapply trnAP|].
          left; exact Hall.
        +++
          eapply in_set_uop_manger_phase_1_elim 
          in Halr; auto;
          destruct Halr as ((q' & Halrl) & Halrr).
          eexists.
          eapply in_set_bop_union_intro;
          [eapply symAP | eapply trnAP | ].
          right; exact Halrl.
      ++
        unfold uop_manger_phase_1, 
        manger_phase_1_auxiliary in Har;
        rewrite manger_merge_set_funex in Har.
        eapply trnP;[exact Har |
        rewrite list_filter_lib_filter_same;
        eapply sum_fn_cong_bop_union_Y].
    + 
      unfold bop_reduce in Ha |- *.
      eapply in_set_uop_manger_phase_1_elim in Ha; 
      auto.
      destruct Ha as ((q & Hal) & Har).
      unfold bSAP in Hal.
      eapply in_set_bop_union_elim in Hal; 
      [|eapply symAP].
      eapply in_set_uop_manger_phase_1_intro;
      auto.
      ++
        destruct Hal as [Hall | Halr].
        +++
          eexists.
          eapply in_set_bop_union_intro;
          [apply symAP | eapply trnAP|].
          left; exact Hall.
        +++
          eexists.
          eapply in_set_bop_union_intro;
          [apply symAP | eapply trnAP|].
          right; eapply in_set_uop_manger_phase_1_intro;
          auto; exists q; exact Halr.
      ++
        unfold uop_manger_phase_1, 
        manger_phase_1_auxiliary in *;
        rewrite manger_merge_set_funex in *.
        eapply trnP;[exact Har |
        rewrite list_filter_lib_filter_same;
        eapply symP, sum_fn_cong_bop_union_Y].
  Qed.


  (* show [P2] is a reduction. 

     Mukesh: I've modified minset_union so that it is now
     compatible with our Manger definitions. 
     So, now we can get the following results about [P2] 
     from more general results about uop_minset and bop_minset_union. 
  *)  
  Lemma P2_cong : uop_congruence _ eqSAP [P2].
  Proof. unfold uop_manger_phase_2.
         apply uop_minset_congruence_weak.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.
  
  Lemma P2_idem : uop_idempotent _ eqSAP [P2].
  Proof. unfold uop_manger_phase_2.
         apply uop_minset_idempotent. 
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
  Qed.

  Lemma P2_left : bop_left_uop_invariant _ eqSAP (bop_reduce [P2] bSAP) [P2].
  Proof. apply minset_union_left_uop_invariant.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.

  Lemma P2_right : bop_right_uop_invariant _ eqSAP (bop_reduce [P2] bSAP) [P2].
  Proof. apply minset_union_right_uop_invariant.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.




 

  Lemma cong_manger_preorder : (brel_congruence (A * P) 
    (brel_product eqA eqP) (manger_pre_order lteA)).
  Proof.
    intros (a, b) (c, d) (u, v) (w, x) Ha Hb.
    cbn. unfold brel_trivial.
    f_equal.
    eapply brel_product_elim in Ha, Hb.
    eapply conLte.
    exact (fst Ha).
    exact (fst Hb).
  Qed.


  Lemma ref_manger_pre_order :
    (brel_reflexive (A * P) (manger_pre_order lteA)).
  Proof.
   intros (a, b).
   cbn.
   rewrite refLte;
   unfold brel_trivial;
   reflexivity.
  Qed.
  
  Lemma tran_manger_pre_order : 
    brel_transitive (A * P) (manger_pre_order lteA).
  Proof.
    intros (a, b) (c, d) (e, f) Ha Hb;
    cbn in Ha, Hb |- *.
    unfold brel_trivial in Ha, Hb |- *;
    rewrite Bool.andb_true_r in Ha, Hb |- *.
    rewrite trnLte;
    [reflexivity | exact Ha | exact Hb].
  Qed.




  

 


  Lemma set_are_eq_reduce : 
    forall (X : finite_set (A * P)) a p,
    (∀ t : A * P,
      in_set (brel_product eqA eqP) X t = true ->
      theory.below (manger_pre_order lteA) (a, p) t = false) ->
    (List.filter (λ '(x, _), eqA x a) X) =S= 
    (List.filter (λ '(x, _), eqA x a) 
        (uop_minset (manger_pre_order lteA) X)).
  Proof.
    intros * Ha.
    eapply brel_set_intro_prop.
    + exact refAP.
    +
      split.
      ++
        intros (au, bu) Hb.
        rewrite list_filter_lib_filter_same in Hb |- *.
        eapply in_set_filter_elim in Hb.
        destruct Hb as [Hbl Hbr].
        * 
          eapply in_set_filter_intro;
          [eapply symAP | eapply bop_congruence_bProp_fst| ].
          split;
          [exact Hbl |].
          eapply in_minset_intro;
          [eapply refAP | eapply symAP | eapply cong_manger_preorder |
          eapply ref_manger_pre_order |].
          split;
          [exact Hbr | intros (ta, tb) Hc].
          specialize (Ha _ Hc).
          eapply theory.below_false_intro.
          eapply theory.below_false_elim in Ha.
          destruct Ha as [Ha | Ha].
          **
            left; rewrite <- Ha.
            unfold manger_pre_order, brel_product,
            brel_trivial in Ha |- *;
            repeat rewrite Bool.andb_true_r in |- *.
            eapply conLte;
            [eapply refA | exact Hbl].
          **
            right; rewrite <-Ha.
            unfold manger_pre_order, brel_product,
            brel_trivial in |- *;
            repeat rewrite Bool.andb_true_r in |- *.
            eapply conLte;
            [exact Hbl | eapply refA].
        *
          eapply bop_congruence_bProp_fst.
      ++
        intros (au, bu) Hb.
        rewrite list_filter_lib_filter_same in Hb |- *.
        eapply in_set_filter_elim in Hb;
        [|eapply bop_congruence_bProp_fst].
        destruct Hb as [Hbl Hbr].
        eapply in_minset_elim in Hbr;
        [|eapply refAP | eapply symAP | eapply cong_manger_preorder|
        eapply ref_manger_pre_order | eapply tran_manger_pre_order ].
        eapply in_set_filter_intro;
        [eapply symAP | eapply bop_congruence_bProp_fst|].
        split;
        [exact Hbl | ].
        destruct Hbr as (Hbrl & Hbrr).
        exact Hbrl.
  Qed.
      



          

  (* In this proof, let's not unfold uop_minset *)
  Lemma matrix_algorithm_addP : 
    forall (X : finite_set (A * P)) a p,
    (∀ t : A * P,
      in_set (brel_product eqA eqP) X t = true ->
      theory.below (manger_pre_order lteA) (a, p) t = false) ->
    eqP 
    (matrix_algorithms.sum_fn zeroP addP 
      snd (List.filter (λ '(x, _), eqA x a) X))
    (matrix_algorithms.sum_fn zeroP addP snd
      (List.filter (λ '(x, _), eqA x a) 
        (uop_minset (manger_pre_order lteA) X))) = true.
  Proof.
    intros * Ha.
    pose proof set_are_eq_reduce X a p Ha as Hb.
    remember (List.filter (λ '(x, _), eqA x a) X) as Xa.
    remember (List.filter (λ '(x, _), eqA x a)
      (uop_minset (manger_pre_order lteA) X)) as Xb.
    eapply sum_fn_congruence_general_set;
    try assumption.
  Qed.
     

   (* 
    Tim: Now, show that the two reductions commute! 
    **** I hope this is true! *****
    Seems true but difficult.

    Mukesh: yes, it's true and difficult as well.
    
  *)

  Lemma P1_P2_commute : ∀ X, ([P2] ([P1] X)) =S= ([P1] ([P2] X)).
  Proof.
    intros ?.
    eapply brel_set_intro_prop.
    + exact refAP.
    +
      split.
      ++
        intros (a, p) Ha.
        eapply in_set_uop_manger_phase_2_elim in Ha;
        try assumption.
        destruct Ha as (Hal & Har).
        (* from Hal we know that 
        *)
        eapply in_set_uop_manger_phase_1_elim 
        with (zeroP := zeroP) in Hal;
        try assumption.
        destruct Hal as ((qt & Hall) & Halr).
        (*  from Halr we know that sum of 
        all 'a's is equal to p *)
        (* now apply intro rule in the goal *)
        eapply in_set_uop_manger_phase_1_intro with 
        (zeroP := zeroP);
        try assumption.
        (* What should be q ?? 
        What is uop_manger_phase_2 is doing? *)
        eexists.
        eapply in_set_uop_manger_phase_2_intro;
        try assumption.
        exact Hall.
        intros * Hb.
        eapply Har.
        eapply in_set_uop_manger_phase_1_intro 
        with (zeroP := zeroP); try assumption.
        exists q; exact Hb.
        instantiate (1 :=
        (matrix_algorithms.sum_fn zeroP addP snd 
          (List.filter (λ '(x, _), eqA x b) X)));
        eapply refP.
        rewrite <-list_filter_lib_filter_same in 
        Halr.
        (* comment *)
        unfold uop_manger_phase_2.
        (* from Har, I can infer below *)
        assert (Hc : ∀ (b : A) (q : P),
          in_set (brel_product eqA eqP) X (b, q) = true → 
          theory.below lteA a b = false).
        intros * Ha. eapply Har.
        eapply in_set_uop_manger_phase_1_intro
        with (zeroP := zeroP); try assumption.
        exists q; exact Ha.
        instantiate (1 :=
        (matrix_algorithms.sum_fn zeroP addP snd 
          (List.filter (λ '(x, _), eqA x b) X)));
        eapply refP.
        (* think! *)
        assert (He : ∀ t : A * P,
          in_set (brel_product eqA eqP) X t = true → 
          theory.below (manger_pre_order lteA) (a, p) t = false).
        intros (c, d) He.
        specialize (Hc c d He).
        eapply theory.below_false_elim in Hc.
        eapply theory.below_false_intro.
        destruct Hc as [Hc | Hc].
        left; cbn; rewrite Hc; reflexivity.
        right; cbn; rewrite Hc; reflexivity. 
        (* end comment here *)
        eapply trnP.
        exact Halr.
        eapply matrix_algorithm_addP.
        exact He.
      ++
        intros (a, p) Ha.
        eapply in_set_uop_manger_phase_1_elim 
        with (zeroP := zeroP) in Ha;
        try assumption.
        destruct Ha as ((qt & Hal) & Har).
        eapply in_set_uop_manger_phase_2_elim in Hal;
        try assumption.
        destruct Hal as (Hall & Halr).
        eapply in_set_uop_manger_phase_2_intro;
        try assumption.
        +++
          eapply in_set_uop_manger_phase_1_intro
          with (zeroP := zeroP); try assumption.
          exists qt; exact Hall.
          unfold uop_manger_phase_2 in Har.
          pose proof in_minset_implies_in_set
          (A * P) (brel_product eqA eqP)
          symAP (manger_pre_order lteA) as Hb.
          rewrite <-list_filter_lib_filter_same in Har.
          (* comment here *)

          assert (He : ∀ t : A * P,
          in_set (brel_product eqA eqP) X t = true → 
          theory.below (manger_pre_order lteA) (a, p) t = false).
          intros (c, d) He.
          specialize (Halr c d He).
          eapply theory.below_false_elim in Halr.
          eapply theory.below_false_intro.
          destruct Halr as [Hc | Hc].
          left; cbn; rewrite Hc; reflexivity.
          right; cbn; rewrite Hc; reflexivity.
         
          (* end comment *)
          eapply trnP;
          [exact Har | eapply symP, matrix_algorithm_addP].
          exact He.
        +++
          intros * Hb.
          eapply in_set_uop_manger_phase_1_elim 
          with (zeroP := zeroP) in Hb; try assumption.
          destruct Hb as ((qp & Hbl) & Hbr).
          eapply Halr; exact Hbl.
    Qed.

    

  (* Given the above lemmas, we can now use the results of 
     cas/coq/uop/commutative_composition.v to 
     prove everything we need to build a 
     commutative and idempotent semigroup. 
     (Note : ignoring existence of id and ann for now ...) 
   *)

  Definition uop_manger := uop_compose [P2] [P1].
  Definition eq_manger :=  brel_reduce eqSAP uop_manger. 
  Definition bop_manger := bop_reduce uop_manger bSAP.

  (* to show non-selectivity of the reduced semigroup we need to prove some things about the witness for 
     non-selectivity of bSAP. 
  *) 
  Lemma fst_nsel_witness_is_fixed_point : let (s, _) := projT1 bSAP_not_selective in uop_manger s =S= s.
  Proof. unfold bSAP_not_selective.
         destruct ntot as [[a1 a2] [L R]]. simpl.
         compute. 
         rewrite refA. rewrite refP. rewrite refA. rewrite refP. reflexivity.
  Qed. 

  Lemma snd_nsel_witness_is_fixed_point : let (_, s) := projT1 bSAP_not_selective in uop_manger s =S= s.
  Proof. unfold bSAP_not_selective.
         destruct ntot as [[a1 a2] [L R]]. simpl.
         compute. 
         rewrite refA. rewrite refP. rewrite refA. rewrite refP. reflexivity.
  Qed. 

  

  Lemma uop_manger_is_reduction : bop_uop_invariant eqSAP bSAP uop_manger.
  Proof. apply uop_compose_is_reduction.
         - exact symSAP. 
         - exact trnSAP. 
         - exact P1_cong. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

  Lemma bop_manger_congruence :
    bop_congruence _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_congruence. 
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

  Lemma bop_manger_associative :
    bop_associative _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_associative.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact bSAP_associative.           
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

    Lemma bop_manger_commutative :
    bop_commutative _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_commutative.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute.
         - exact bSAP_commutative. 
  Qed. 
 
  Lemma bop_manger_idempotent :
    bop_idempotent _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_idempotent.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute.
         - exact bSAP_idempotent. 
  Qed. 

  Lemma bop_manger_not_selective :
    bop_not_selective _ eq_manger bop_manger.
  Proof.
    destruct ntot as ((a₁, a₂) & Ha).
    exists ([(a₁, wP)], [(a₂, wP)]);
    cbn; unfold eq_manger, brel_reduce,
    uop_manger, uop_compose, 
    uop_manger_phase_2, uop_manger_phase_1, 
    uop_minset, manger_phase_1_auxiliary,
    bop_manger, bop_reduce, 
    uop_manger, uop_manger_phase_1; cbn.
    case_eq (and.bop_and (eqA a₁ a₂) (eqP wP wP));
    intros Hb; cbn.
    ++
      eapply Bool.andb_true_iff in Hb.
      destruct Hb as (Hbl & Hbr).
      destruct Ha as (Hal & Har).
      split.
      +++
        unfold eqSAP, brel_set, 
        brel_and_sym, brel_subset; cbn;
        rewrite Hbl, refP; cbn.
        rewrite (symA _ _ Hbl); cbn.
        (* true = false *)
        (* it's contradiction, but I don't have 
          suitable axiom to discharge it. 
          From Hbl I know that a₁ and a₂ are 
          equivalent, but refLte is not general 
          enough. It should be 
          ∀ a₁ a₂, eqA a₁ a₂ = true -> lteA a₁ a₂ = true. 
        *)
        assert (Hd := conLte _ _ _ _ (refA a₁) Hbl).
        rewrite <-Hd in Hal.
        rewrite (refLte a₁) in Hal; congruence.
      +++
        unfold eqSAP, brel_set, 
        brel_and_sym, brel_subset; cbn.
        rewrite refA, refP; cbn.
        (* true = false *)
        (* Same as above. *)
        assert (Hd := conLte _ _ _ _ (refA a₁) Hbl).
        rewrite <-Hd in Hal.
        rewrite (refLte a₁) in Hal; congruence.
    ++
      unfold uop_compose; cbn.
      eapply Bool.andb_false_iff in Hb.
      destruct Hb as [Hb | Hbr].
      +++
        assert (Hc : eqA a₂ a₁ = false). 
        case_eq (eqA a₂ a₁); intro Hc;
        try reflexivity. 
        rewrite (symA _ _ Hc) in Hb; 
        congruence.
        rewrite Hc.
        unfold uop_manger_phase_2,
        uop_minset. cbn.
        unfold theory.below; cbn.
        destruct Ha as [Hal Har].
        rewrite Hal, Har; cbn.
        rewrite Hb; cbn.
        unfold theory.below; cbn.
        rewrite Hal, Har; cbn.
        split.
        *
          unfold eqSAP, brel_set, 
          brel_and_sym, brel_subset; cbn.
          rewrite Hb, Hc, refA, refP; cbn;
          reflexivity.
        *
          unfold eqSAP, brel_set, 
          brel_and_sym, brel_subset; cbn.
          rewrite Hb, Hc, refA, refP; cbn;
          reflexivity.
      +++
        rewrite refP in Hbr;
        congruence.
  Qed.
          

End Theory.   

