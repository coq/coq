(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Product of two integration spaces and Fubini's theorem.

    As a naive approach, we can think of taking linear combinations of
    products of integrable functions as L-functions, and I linear.
    However this fails to be stable stability under absolute value.
    We work around this problem by taking products of integrable
    characteristic functions, which linear combinations can be split
    on disjoint rectangles. Then we can take the absolute of those
    disjoint coefficients. *)

Require Import QArith_base.
Require Import List.
Require Import ConstructiveReals.
Require Import ConstructiveRealsMorphisms.
Require Import ConstructiveAbs.
Require Import ConstructiveLimits.
Require Import ConstructivePartialFunctions.
Require Import CMTbase.
Require Import CMTIntegrableFunctions.
Require Import CMTIntegrableSets.
Require Import CMTFullSets.
Require Import CMTcast.
Require Import CMTprofile.

Local Open Scope ConstructiveReals.



(* An element of a product L-function, ie a product of integrable sets,
   multiplied by a real number. Its elementary integral is the product
   of measures, multiplied by the real number. *)
Record ProdIntegrable {I J : IntegrationSpace} : Type :=
  { prodint_f : X (ElemFunc I) -> Prop;
    prodint_g : X (ElemFunc J) -> Prop;
    prodint_factor : CRcarrier (RealT (ElemFunc I));
    prodint_fint : IntegrableSet prodint_f;
    prodint_gint : IntegrableSet prodint_g;
  }.

(* Tensor product of prodint_f and prodint_g. *)
Definition ProdIntegrableFunc {I J : IntegrationSpace}
           (fg : @ProdIntegrable I J)
  : @PartialFunction (RealT (ElemFunc I)) (* Convert in the first real type. *)
                     (prod (X (ElemFunc I)) (X (ElemFunc J))).
Proof.
  apply (Build_PartialFunctionXY
           (prod (X (ElemFunc I)) (X (ElemFunc J)))
           (CRcarrier (RealT (ElemFunc I))) (CReq (RealT (ElemFunc I)))
           (* This domain is smaller than just deciding the rectangle,
              because we decide both coordinates. It is necessary
              to subdivide a union of rectangles into a disjoint
              grid of rectangles. See ProdIntegrableSimplify below. *)
           (fun xy => prod (Domain (CharacFunc (prodint_f fg)) (fst xy))
                        (Domain (@CharacFunc (RealT (ElemFunc I)) _ (prodint_g fg)) (snd xy)))
           (fun xy xyD => prodint_factor fg
                       * partialApply _ (fst xy) (fst xyD)
                       * partialApply _ (snd xy) (snd xyD))).
  intros [x y] p q. destruct p,q; simpl.
  do 2 rewrite CRmult_assoc. apply CRmult_morph.
  reflexivity. destruct d,d0,d1,d2; try reflexivity; try contradiction.
Defined.

(* A product L-function, ie a linear combination of ProdIntegrable. *)
Definition ProdLFunc {I J : IntegrationSpace}
  : list (@ProdIntegrable I J)
    -> PartialFunction (prod (X (ElemFunc I)) (X (ElemFunc J)))
  := fun l => XsumList (map ProdIntegrableFunc l).

Definition ProdIntegrableZero (I J : IntegrationSpace)
  : @ProdIntegrable I J.
Proof.
  apply (Build_ProdIntegrable
           I J (fun x => False) (fun y => False) 0).
  - apply (IntegrableFunctionExtensional
             (Xconst (X (ElemFunc I)) 0)).
    split.
    + intros x _. right. intro abs. contradiction.
    + intros. simpl. destruct xG. contradiction. reflexivity.
    + apply IntegrableZero.
  - apply (IntegrableFunctionExtensional
             (Xconst (X (ElemFunc J)) 0)).
    split.
    + intros x _. right. intro abs. contradiction.
    + intros. simpl. destruct xG. contradiction. reflexivity.
    + apply IntegrableZero.
Defined.

Lemma DomainProdLFuncInc
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyS : Domain (ProdLFunc hn) (x,y))
      (n : nat),
    lt n (length hn)
    -> Domain (ProdIntegrableFunc (nth n hn (ProdIntegrableZero I J))) (x,y).
Proof.
  induction hn.
  - intros. exfalso; inversion H.
  - intros. simpl in H. destruct n.
    + apply xyS.
    + apply le_S_n in H. simpl. apply (IHhn x y).
      apply xyS. exact H.
Qed.

Lemma DomainProdLFuncIncReverse
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J)),
    (forall n:nat, lt n (length hn)
            -> Domain (ProdIntegrableFunc (nth n hn (ProdIntegrableZero I J))) (x,y))
    -> Domain (ProdLFunc hn) (x,y).
Proof.
  induction hn.
  - intros. simpl. trivial.
  - intros x y H. split.
    + apply (H O). apply le_n_S, le_0_n.
    + apply IHhn. intros. apply le_n_S in H0.
      exact (H (S n) H0).
Qed.

Lemma DomainProdLFuncAppLeft
  : forall {I J : IntegrationSpace}
      (l k : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J)),
    Domain (ProdLFunc (l ++ k)) (x,y)
    -> Domain (ProdLFunc l) (x, y).
Proof.
  induction l.
  - intros. simpl. trivial.
  - intros k x y H. destruct H. split. exact d.
    exact (IHl k x y d0).
Qed.

Lemma DomainProdLFuncAppRight
  : forall {I J : IntegrationSpace}
      (l k : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J)),
    Domain (ProdLFunc (l ++ k)) (x,y)
    -> Domain (ProdLFunc k) (x, y).
Proof.
  induction l.
  - intros l x y H. exact H.
  - intros k x y H. destruct H.
    exact (IHl k x y d0).
Qed.

Lemma ApplyProdLFuncApp
  : forall {I J : IntegrationSpace}
      (l k : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyL : Domain (ProdLFunc l) (x,y))
      (xyK : Domain (ProdLFunc k) (x,y))
      (xyDS : Domain (ProdLFunc (l ++ k)) (x,y)),
    partialApply (ProdLFunc (l ++ k)) (x, y) xyDS
    == partialApply (ProdLFunc l) (x,y) xyL
       + partialApply (ProdLFunc k) (x,y) xyK.
Proof.
  induction l as [|a l].
  - intros. simpl (partialApply (ProdLFunc nil) (x, y) xyL).
    rewrite CRplus_0_l. apply DomainProp.
  - intros. simpl. destruct xyDS, d, xyL, d2. simpl.
    rewrite CRplus_assoc. apply CRplus_morph.
    + destruct d. destruct d2. 2: contradiction.
      destruct d1. destruct d4. 2: contradiction. reflexivity.
      destruct d4. contradiction. reflexivity.
      rewrite CRmult_0_r, CRmult_0_l.
      destruct d2. contradiction.
      rewrite CRmult_0_r, CRmult_0_l. reflexivity.
    + apply IHl.
Qed.


(* A product L-function is simple when its sum is on disjoint rectangles.
   But more convenient to sum on a disjoint grid. *)

(* Computes a list of size 2^n, of lists of size n,
   with all possible combinations.
   Will be used to sum on all subsets later.
   We could also have used natural numbers to represent subset,
   with their binary digits as the lists of bool. *)
Fixpoint FreeSubsets (n : nat) : list (list bool)
  := match n with
     | O => nil :: nil
     | S p => map (fun l => true :: l) (FreeSubsets p)
                  ++ map (fun l => false :: l) (FreeSubsets p)
     end.

Lemma FreeSubsetsNotNil : forall n : nat, FreeSubsets n <> nil.
Proof.
  induction n.
  - discriminate.
  - simpl. intro abs. apply app_eq_nil in abs.
    destruct abs. apply map_eq_nil in H. exact (IHn H).
Qed.

Lemma FreeSubsetsLength : forall (n : nat) (l : list bool),
    In l (FreeSubsets n) -> length l = n.
Proof.
  induction n.
  - intros. destruct H. subst l. reflexivity.
    exfalso; inversion H.
  - intros. simpl in H. apply in_app_or in H. destruct H.
    + apply in_map_iff in H. destruct H as [k [H H0]].
      subst l. simpl. rewrite (IHn k). reflexivity. exact H0.
    + apply in_map_iff in H. destruct H as [k [H H0]].
      subst l. simpl. rewrite (IHn k). reflexivity. exact H0.
Qed.

(* Produce a membership proposition in sort Type.
   This is actually the reading of l as the binary
   digits of the number k. *)
Lemma FreeSubsetsFull : forall l : list bool,
    { k : nat | lt k (length (FreeSubsets (length l)))
              /\ nth k (FreeSubsets (length l)) nil = l }.
Proof.
  induction l as [|a l].
  - exists O. split. apply le_refl. reflexivity.
  - simpl. destruct IHl as [k [H H0]]. destruct a.
    + exists k. split. rewrite app_length, map_length, map_length.
      apply (lt_le_trans _ (0+length (FreeSubsets (length l)))).
      exact H. rewrite <- Nat.add_le_mono_r. apply le_0_n.
      rewrite app_nth1.
      rewrite (nth_indep _ nil (true::nil)), map_nth, H0.
      reflexivity. rewrite map_length. exact H.
      rewrite map_length. exact H.
    + exists (k + length (FreeSubsets (length l)))%nat. split.
      rewrite app_length, map_length, map_length.
      rewrite <- Nat.add_lt_mono_r. exact H.
      rewrite app_nth2. rewrite map_length, Nat.add_sub.
      rewrite (nth_indep _ nil (false::nil)), map_nth, H0.
      reflexivity. rewrite map_length. exact H.
      rewrite map_length.
      apply (le_trans _ (0+length (FreeSubsets (length l)))).
      apply le_refl. rewrite <- Nat.add_le_mono_r. apply le_0_n.
Qed.

Lemma FreeSubsetsDifferent : forall (n p q : nat),
    p <> q
    -> lt p (length (FreeSubsets n))
    -> lt q (length (FreeSubsets n))
    -> nth p (FreeSubsets n) nil <> nth q (FreeSubsets n) nil.
Proof.
  induction n.
  - intros. exfalso. simpl in H0. simpl in H1.
    destruct p,q. exact (H eq_refl). apply le_S_n in H1.
    inversion H1. apply le_S_n in H0. inversion H0.
    apply le_S_n in H1. inversion H1.
  - intros. simpl.
    destruct (le_lt_dec (length (FreeSubsets n)) p),
    (le_lt_dec (length (FreeSubsets n)) q).
    + rewrite app_nth2.
      2: rewrite map_length; exact l.
      rewrite app_nth2.
      2: rewrite map_length; exact l0.
      rewrite map_length.
      assert (q - length (FreeSubsets n) < length (FreeSubsets n))%nat.
      { rewrite (Nat.add_lt_mono_r _ _ (length (FreeSubsets n))).
        rewrite Nat.sub_add. 2: exact l0. simpl in H1.
        rewrite app_length, map_length, map_length in H1. exact H1. }
      assert (p - length (FreeSubsets n) < length (FreeSubsets n))%nat.
      { rewrite (Nat.add_lt_mono_r _ _ (length (FreeSubsets n))).
        rewrite Nat.sub_add. 2: exact l. simpl in H0.
        rewrite app_length, map_length, map_length in H0. exact H0. }
      specialize (IHn (p - length (FreeSubsets n))%nat
                      (q - length (FreeSubsets n))%nat).
      rewrite (nth_indep _ nil (false::nil)), (nth_indep _ nil (false::nil)).
      rewrite map_nth, map_nth.
      2: rewrite map_length; exact H2.
      2: rewrite map_length; exact H3.
      intro abs. inversion abs. apply IHn. 2: exact H3. 2: exact H2.
      2: exact H5.
      intro abs2.
      assert ((p - length (FreeSubsets n) + length (FreeSubsets n))%nat
              = (q - length (FreeSubsets n) + length (FreeSubsets n))%nat).
      { rewrite abs2. reflexivity. }
      do 2 rewrite Nat.sub_add in H4. contradiction.
      exact l0. exact l. exact l.
    + clear IHn. rewrite app_nth2.
      2: rewrite map_length; exact l.
      rewrite app_nth1.
      2: rewrite map_length; exact l0.
      rewrite map_length.
      rewrite (nth_indep _ nil (false::nil)), (nth_indep _ nil (true::nil)).
      rewrite map_nth, map_nth. intro abs. inversion abs.
      rewrite map_length. exact l0. rewrite map_length.
      rewrite (Nat.add_lt_mono_r _ _ (length (FreeSubsets n))).
      rewrite Nat.sub_add. 2: exact l. simpl in H0.
      rewrite app_length, map_length, map_length in H0. exact H0.
    + clear IHn. rewrite app_nth1.
      2: rewrite map_length; exact l.
      rewrite app_nth2.
      2: rewrite map_length; exact l0.
      rewrite map_length.
      rewrite (nth_indep _ nil (true::nil)), (nth_indep _ nil (false::nil)).
      rewrite map_nth, map_nth. intro abs. inversion abs.
      rewrite map_length.
      rewrite (Nat.add_lt_mono_r _ _ (length (FreeSubsets n))).
      rewrite Nat.sub_add. 2: exact l0. simpl in H1.
      rewrite app_length, map_length, map_length in H1. exact H1.
      rewrite map_length. exact l.
    + rewrite app_nth1.
      2: rewrite map_length; exact l.
      rewrite app_nth1.
      2: rewrite map_length; exact l0.
      rewrite (nth_indep _ nil (true::nil)), (nth_indep _ nil (true::nil)).
      rewrite map_nth, map_nth.
      intro abs. inversion abs. apply (IHn p q H l l0). exact H3.
      rewrite map_length. exact l0.
      rewrite map_length. exact l.
Qed.

Definition ProdIntegrableDisjoint
           {I J : IntegrationSpace}
           (h k : ProdIntegrable) : Prop
  := forall (x : X (ElemFunc I)) (y : X (ElemFunc J)),
    ~(prodint_f h x /\ prodint_f k x /\ prodint_g h y /\ prodint_g k y).

(* Equivalent to forall i,j < length l, i < j -> P (l i) (l j) *)
Fixpoint forall_disjoint_pairs { X : Type } (l : list X) (P : X -> X -> Prop) : Prop
  := match l with
     | nil => True
     | h::t => forall_disjoint_pairs t P /\ Forall (P h) t
     end.

Lemma forall_disjoint_pairs_equiv
  : forall { X : Type } (l : list X) (P : X -> X -> Prop) (x : X),
    (forall i j : nat, lt i j -> lt j (length l)
                -> P (nth i l x) (nth j l x))
    -> forall_disjoint_pairs l P.
Proof.
  induction l.
  - intros. constructor.
  - intros. split.
    + apply (IHl P x). intros.
      apply (H (S i) (S j)). apply le_n_S, H0.
      apply le_n_S, H1.
    + clear IHl. apply Forall_forall. intros.
      apply (In_nth _ _ a) in H0. destruct H0 as [n [H0 H1]].
      subst x0. specialize (H O (S n)). simpl in H.
      rewrite (nth_indep _ a x). apply H.
      apply le_n_S, le_0_n. apply le_n_S, H0. exact H0.
Qed.

Definition ProdIntegrableSimple
           {I J : IntegrationSpace}
         (hn : list (@ProdIntegrable I J)) : Prop
  := forall_disjoint_pairs hn ProdIntegrableDisjoint.

Definition SubsetUnion {A : Set}
           (hn : list (A -> Prop))
  : A -> Prop
  := fold_right (fun fg acc x => fg x \/ acc x) (fun x => False) hn.

Lemma SubsetUnionLeftDec
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyH : Domain (ProdLFunc hn) (x,y)),
    (SubsetUnion (map prodint_f hn) x /\ ~Forall (fun fg => ~prodint_f fg x) hn)
    \/ (Forall (fun fg => ~prodint_f fg x) hn /\ ~SubsetUnion (map prodint_f hn) x).
Proof.
  induction hn.
  - intros. right. split. apply Forall_nil.
    intro abs. exact abs.
  - intros. destruct xyH. destruct (IHhn x y d0).
    + left. split. right. apply H. intro abs.
      inversion abs. destruct H. contradiction.
    + simpl. destruct d, d. left. split. left. exact p.
      intro abs. inversion abs. destruct H. contradiction.
      right. split. apply Forall_cons. exact n.
      apply H. intro abs. destruct abs.
      contradiction. destruct H. contradiction.
Qed.

(* Intersection of init and hn,
   inside or outside according to filter. *)
Fixpoint SubsetIntersectFilter { A : Set }
         (hn : list (A -> Prop))
         (init : A -> Prop)
         (filter : list bool)
  : A -> Prop
  := match filter with
     | nil => init
     | b :: sub => match hn with
                 | nil => init
                 | p :: h => if b then
                             fun x => p x /\ SubsetIntersectFilter h init sub x
                           else
                             fun x => SubsetIntersectFilter h init sub x /\ ~p x
                 end
     end.

Lemma SubsetIntersectFilterInc
  : forall { A : Set }
      (hn : list (A -> Prop))
      (init biginit : A -> Prop)
      (filter : list bool) (x : A),
    (forall y:A, init y -> biginit y)
    -> SubsetIntersectFilter hn init filter x
    -> SubsetIntersectFilter hn biginit filter x.
Proof.
  induction hn.
  - intros. simpl. simpl in H0. destruct filter.
    apply H, H0. apply H, H0.
  - intros. destruct filter. simpl. apply H, H0.
    simpl. simpl in H0. destruct b. split. apply H0.
    apply (IHhn init). exact H. apply H0.
    split. apply (IHhn init). exact H. apply H0.
    intro abs. destruct H0. contradiction.
Qed.

Definition SubsetIntersectLeft
           {I J : IntegrationSpace}
           (hn : list (@ProdIntegrable I J))
           (init : X (ElemFunc I) -> Prop)
           (filter : list bool)
  : X (ElemFunc I) -> Prop
  := SubsetIntersectFilter (map prodint_f hn) init filter.

Lemma SubsetIntersectFilter_init
  : forall { A : Set }
      (hn : list (A -> Prop)) (init : A -> Prop)
      (filter : list bool) (x : A),
    SubsetIntersectFilter hn init filter x
    -> init x.
Proof.
  induction hn.
  - intros. destruct filter; exact H.
  - intros. destruct filter. exact H. simpl in H.
    destruct b; apply (IHhn init filter), H.
Qed.

Lemma SubsetUnionLeftIntegrable
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J)),
    IntegrableSet (SubsetUnion (map prodint_f hn)).
Proof.
  induction hn.
  - apply (IntegrableFunctionExtensional
             (Xconst (X (ElemFunc I)) 0)).
    split.
    + intros x _. right. intro abs. contradiction.
    + intros. simpl. destruct xG. contradiction. reflexivity.
    + apply IntegrableZero.
  - apply IntegrableSetUnion. apply a. apply IHhn.
Qed.

Lemma SubsetIntersectLeftIntegrable
  : forall {I J : IntegrationSpace}
      (subset : list bool) (init : X (ElemFunc I) -> Prop)
      (hn : list (@ProdIntegrable I J)),
    IntegrableSet init
    -> IntegrableSet (SubsetIntersectLeft hn init subset).
Proof.
  induction subset as [|a subset].
  - intros init hn initInt. destruct hn; exact initInt.
  - intros. simpl. destruct hn as [|p hn].
    exact X. destruct a. apply IntegrableSetIntersect. apply p.
    apply IHsubset. exact X. apply IntegrableSetDifference.
    apply IHsubset. exact X. apply p.
Qed.

Lemma SubsetUnionRightDec
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyH : Domain (ProdLFunc hn) (x,y)),
    (SubsetUnion (map prodint_g hn) y /\ ~Forall (fun fg => ~prodint_g fg y) hn)
    \/ (Forall (fun fg => ~prodint_g fg y) hn /\ ~SubsetUnion (map prodint_g hn) y).
Proof.
  induction hn.
  - intros. right. split. apply Forall_nil.
    intro abs. exact abs.
  - intros. destruct xyH. destruct (IHhn x y d0).
    + left. split. right. apply H.
      intro abs. inversion abs. destruct H. contradiction.
    + simpl. destruct d, d1. left. split.
      left. exact p. intro abs.
      inversion abs. destruct H. contradiction.
      right. split. apply Forall_cons. exact n. apply H.
      intro abs. destruct abs. contradiction. destruct H. contradiction.
Qed.

Definition SubsetIntersectRight
           {I J : IntegrationSpace}
           (hn : list (@ProdIntegrable I J))
           (init : X (ElemFunc J) -> Prop)
           (filter : list bool)
  : X (ElemFunc J) -> Prop
  := SubsetIntersectFilter (map prodint_g hn) init filter.

Lemma SubsetUnionRightIntegrable
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J)),
    IntegrableSet (SubsetUnion (map prodint_g hn)).
Proof.
  induction hn.
  - apply (IntegrableFunctionExtensional
             (Xconst (X (ElemFunc J)) 0)).
    split.
    + intros x _. right. intro abs. contradiction.
    + intros. simpl. destruct xG. contradiction. reflexivity.
    + apply IntegrableZero.
  - apply IntegrableSetUnion. apply a. apply IHhn.
Qed.

Lemma SubsetIntersectRightIntegrable
  : forall {I J : IntegrationSpace}
      (subset : list bool) (init : X (ElemFunc J) -> Prop)
      (hn : list (@ProdIntegrable I J)),
    IntegrableSet init
    -> IntegrableSet (SubsetIntersectRight hn init subset).
Proof.
  induction subset as [|a subset].
  - intros init hn initInt. destruct hn; exact initInt.
  - intros. simpl. destruct hn as [|p hn].
    exact X. destruct a. apply IntegrableSetIntersect. apply p.
    apply IHsubset. exact X. apply IntegrableSetDifference.
    apply IHsubset. exact X. apply p.
Qed.

(* Sum all factors that are activated by subsetf and subsetg. *)
Fixpoint SubsetIntersectFactor
         {I J : IntegrationSpace}
         (hn : list (@ProdIntegrable I J))
         (subsetf subsetg : list bool) {struct subsetf}
  : CRcarrier (RealT (ElemFunc I))
  := match subsetf, subsetg, hn with
     | sf::tf, sg::tg, h::t
       => SubsetIntersectFactor t tf tg
         + (if andb sf sg then prodint_factor h else 0)
     | _, _, _ => 0
     end.

(* If subsetf or subsetg is all false, the intersection of the
   corresponding complements can be not integrable. Bound it
   by the union of the subsets. *)
Definition ProdSubsetIntersect
           {I J : IntegrationSpace}
           (hn : list (@ProdIntegrable I J))
           (subsetf subsetg : list bool)
  : @ProdIntegrable I J.
Proof.
  (* When the subsets are all false, it means the domain outside
     all of hn which is not necessarily integrable, but then
     it is assigned the coefficient zero. *)
  intros.
  apply (Build_ProdIntegrable
           I J
           (SubsetIntersectLeft hn (SubsetUnion (map prodint_f hn)) subsetf)
           (SubsetIntersectRight hn (SubsetUnion (map prodint_g hn)) subsetg)
           (SubsetIntersectFactor hn subsetf subsetg)).
  apply SubsetIntersectLeftIntegrable.
  apply SubsetUnionLeftIntegrable.
  apply SubsetIntersectRightIntegrable.
  apply SubsetUnionRightIntegrable.
Defined.

Lemma nth_list_prod : forall {A B : Type} (l:list A) (k:list B) (a:A) (b:B) (n:nat),
    lt n (length l * length k)
    -> nth n (list_prod l k) (a,b)
      = (nth (n / length k) l a, nth (n mod (length k)) k b).
Proof.
  induction l.
  - intros. exfalso; inversion H.
  - intros. destruct (le_lt_dec (length k) n).
    + assert (n - length k < length l * length k)%nat.
      { rewrite (Nat.add_lt_mono_r _ _ (length k)), Nat.sub_add.
        2: exact l0. rewrite Nat.add_comm. exact H. }
      specialize (IHl k a0 b (n - length k)%nat H0). clear H.
      simpl (list_prod (a :: l) k).
      rewrite app_nth2.
      2: rewrite map_length; exact l0.
      rewrite map_length. rewrite IHl.
      pose proof (Nat.le_exists_sub (length k) n l0) as [i [H _]].
      subst n. rewrite Nat.add_sub. apply f_equal2.
      replace ((i + length k) / length k)%nat with (S (i / length k))%nat.
      reflexivity. replace (i + length k)%nat with (i + 1*length k)%nat.
      rewrite Nat.div_add. rewrite Nat.add_comm. reflexivity.
      2: rewrite Nat.mul_1_l; reflexivity.
      intro abs. rewrite Nat.add_sub, abs, Nat.mul_0_r in H0. inversion H0.
      replace (i + length k)%nat with (i + 1*length k)%nat.
      rewrite Nat.mod_add. reflexivity.
      intro abs. rewrite Nat.add_sub, abs, Nat.mul_0_r in H0. inversion H0.
      rewrite Nat.mul_1_l. reflexivity.
    + clear IHl. simpl (list_prod (a :: l) k). rewrite app_nth1.
      2: rewrite map_length; exact l0.
      rewrite Nat.div_small, Nat.mod_small. 2: exact l0. 2: exact l0.
      simpl. rewrite (nth_indep _ (a0,b) (a,b)).
      rewrite map_nth. reflexivity. rewrite map_length. exact l0.
Qed.

Lemma DomainProdSubsetIntersect
  : forall {A : Set}
      (hn : list (A -> Prop))
      (init : A -> Prop)
      (l : list bool) (x : A) (n : nat),
    SubsetIntersectFilter hn init l x
    -> match nth_error hn n, nth_error l n with
      | Some fg, Some b
        => if b then fg x else ~fg x
      | _, _ => True
      end.
Proof.
  induction hn.
  - intros. destruct n; simpl; trivial.
  - intros. destruct n.
    + simpl. destruct l as [|b l]. trivial.
      destruct b; apply H.
    + simpl. destruct l as [|b l].
      destruct (nth_error hn n); trivial. apply (IHhn init l).
      simpl in H. destruct b; apply H.
Qed.

Lemma SubsetsDifferent : forall (h k : list bool),
    length h = length k
    -> h <> k
    -> { n : nat | lt n (length h) /\ nth_error h n <> nth_error k n }.
Proof.
  induction h.
  - intros. exfalso. destruct k. exact (H0 eq_refl). inversion H.
  - intros. destruct k. exfalso; inversion H. simpl in H.
    inversion H. clear H. destruct a, b.
    + destruct (IHh k H2) as [n [nlen ndiff]].
      intro abs. subst k. exact (H0 eq_refl).
      exists (S n). split. apply le_n_S, nlen. exact ndiff.
    + exists O. split. apply le_n_S, le_0_n. simpl. discriminate.
    + exists O. split. apply le_n_S, le_0_n. simpl. discriminate.
    + destruct (IHh k H2) as [n [nlen ndiff]].
      intro abs. subst k. exact (H0 eq_refl).
      exists (S n). split. apply le_n_S, nlen. exact ndiff.
Qed.

Lemma ProdIntegrableSubsetsDisjoint
  : forall {A : Set}
      (hn : list (A -> Prop))
      (l l0 : list bool)
      (x : A),
    length l = length l0
    -> length l = length hn
    -> l <> l0
    -> ~ (SubsetIntersectFilter hn (SubsetUnion hn) l x
         /\ SubsetIntersectFilter hn (SubsetUnion hn) l0 x).
Proof.
  intros. simpl. intros [H2 H3].
  pose proof (SubsetsDifferent l l0 H H1) as [n [nlen ndiff]].
  pose proof (DomainProdSubsetIntersect
                hn (SubsetUnion hn) l x n H2).
  pose proof (DomainProdSubsetIntersect
                hn (SubsetUnion hn) l0 x n H3).
  destruct (nth_error hn n) eqn:des.
  destruct (nth_error l n) eqn:desl. destruct (nth_error l0 n) eqn:des0.
  destruct b. destruct b0. exact (ndiff eq_refl). contradiction.
  destruct b0. contradiction. exact (ndiff eq_refl).
  rewrite nth_error_None, <- H in des0.
  exact (lt_not_le _ _ nlen des0).
  rewrite nth_error_None in desl.
  exact (lt_not_le _ _ nlen desl).
  rewrite nth_error_None, <- H0 in des.
  exact (lt_not_le _ _ nlen des).
Qed.

Definition ProdIntegrableSimplify
           {I J : IntegrationSpace}
         (hn : list (@ProdIntegrable I J))
  : list (@ProdIntegrable I J)
  := map (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))
         (list_prod (FreeSubsets (length hn)) (FreeSubsets (length hn))).

Lemma nat_euclid_unique : forall i j q : nat,
    lt 0 q
    -> (i / q = j / q)%nat
    -> i mod q = j mod q
    -> i = j.
Proof.
  intros. assert (q <> O).
  { destruct q. exfalso; exact (lt_irrefl O H). discriminate. }
  rewrite (Nat.div_mod j q H2), <- H1, <- H0.
  apply Nat.div_mod, H2.
Qed.

Lemma ProdIntegrableSimplifyDisjoint
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J)),
    ProdIntegrableSimple (ProdIntegrableSimplify hn).
Proof.
  intros.
  apply (forall_disjoint_pairs_equiv
           _ _ (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                          (snd (@nil bool, nil)))).
  intros.
  unfold ProdIntegrableSimplify in H0. rewrite map_length, prod_length in H0.
  assert (0 < length (FreeSubsets (length hn)))%nat as lenPos.
  { destruct (length (FreeSubsets (length hn))).
    exfalso; inversion H0. apply le_n_S, le_0_n. }
  unfold ProdIntegrableSimplify.
  do 2 rewrite (map_nth (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))
                   _ (@nil bool, @nil bool)).
  rewrite (nth_list_prod
                (FreeSubsets (length hn)) (FreeSubsets (length hn)) nil nil i
                (lt_trans _ _ _ H H0)).
  rewrite (nth_list_prod
                (FreeSubsets (length hn)) (FreeSubsets (length hn)) nil nil j H0).
  unfold fst, snd.
  (* Decompose i,j into product pairs of indices (a,b), (c,d). *)
  remember (i / length (FreeSubsets (length hn)))%nat as a.
  remember (i mod (length (FreeSubsets (length hn))))%nat as b.
  remember (j / length (FreeSubsets (length hn)))%nat as c.
  remember (j mod (length (FreeSubsets (length hn))))%nat as d.
  intros x y z. simpl in z. destruct z as [xH [xK [yH yK]]].
  destruct (Nat.eq_dec a c).
  - (* If subsets b and d are different, the product on y's is zero. *)
    assert (b <> d).
    { intro abs. subst d. subst b. subst c. subst a.
      rewrite (nat_euclid_unique _ _ _ lenPos e abs) in H.
      exact (lt_irrefl j H). }
    assert (d < length (FreeSubsets (length hn)))%nat as din.
    { subst d. apply Nat.mod_upper_bound.
      intro abs. rewrite abs in lenPos. exact (lt_irrefl _ lenPos). }
    apply (ProdIntegrableSubsetsDisjoint
             (map prodint_g hn) (nth d (FreeSubsets (length hn)) nil)
             (nth b (FreeSubsets (length hn)) nil) y).
    4: split; assumption.
    rewrite (FreeSubsetsLength (length hn)).
    rewrite (FreeSubsetsLength (length hn)). reflexivity.
    apply nth_In. subst b. apply Nat.mod_upper_bound.
    intro abs. rewrite abs in lenPos. exact (lt_irrefl _ lenPos).
    apply nth_In. exact din.
    rewrite (FreeSubsetsLength (length hn)).
    rewrite map_length. reflexivity.
    apply nth_In. exact din.
    apply FreeSubsetsDifferent.
    intro abs. apply H1. symmetry. exact abs. exact din.
    subst b. apply Nat.mod_upper_bound.
    intro abs. rewrite abs in lenPos. exact (lt_irrefl _ lenPos).
  - (* If subsets a and c are different, the product on x's is zero. *)
    assert (c < length (FreeSubsets (length hn)))%nat as cin.
    { subst c.
      apply Nat.div_lt_upper_bound. intro abs.
      rewrite abs in lenPos. exact (lt_irrefl 0 lenPos). exact H0. }
    apply (ProdIntegrableSubsetsDisjoint
             (map prodint_f hn) (nth c (FreeSubsets (length hn)) nil)
             (nth a (FreeSubsets (length hn)) nil) x).
    4: split; assumption. clear xH xK yH yK.
    rewrite (FreeSubsetsLength (length hn)).
    rewrite (FreeSubsetsLength (length hn)). reflexivity.
    apply nth_In. subst a.
    apply Nat.div_lt_upper_bound. intro abs.
    rewrite abs in lenPos. exact (lt_irrefl 0 lenPos).
    exact (lt_trans _ _ _ H H0).
    apply nth_In. exact cin.
    rewrite (FreeSubsetsLength (length hn)).
    rewrite map_length. reflexivity. apply nth_In. exact cin.
    apply FreeSubsetsDifferent.
    intro abs. apply n. symmetry. exact abs. exact cin.
    subst a.
    apply Nat.div_lt_upper_bound. intro abs.
    rewrite abs in lenPos. exact (lt_irrefl 0 lenPos).
    exact (lt_trans _ _ _ H H0).
Qed.

Fixpoint ProdIntegrableSubsetLeft
         {I J : IntegrationSpace}
         (hn : list (@ProdIntegrable I J))
         (x : X (ElemFunc I)) (y : X (ElemFunc J))
         (xyH : Domain (ProdLFunc hn) (x,y)) { struct hn }
  : list bool.
Proof.
  destruct hn.
  - exact nil.
  - destruct xyH, d.
    exact ((if d then true else false) :: ProdIntegrableSubsetLeft I J hn x y d0).
Defined.

Lemma ProdIntegrableSubsetLeft_length
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyH : Domain (ProdLFunc hn) (x,y)),
    length (ProdIntegrableSubsetLeft hn x y xyH) = length hn.
Proof.
  induction hn.
  - reflexivity.
  - intros. simpl. destruct xyH, d. simpl.
    rewrite IHhn. reflexivity.
Qed.

Fixpoint ProdIntegrableSubsetRight
         {I J : IntegrationSpace}
         (hn : list (@ProdIntegrable I J))
         (x : X (ElemFunc I)) (y : X (ElemFunc J))
         (xyH : Domain (ProdLFunc hn) (x,y)) { struct hn }
  : list bool.
Proof.
  destruct hn.
  - exact nil.
  - destruct xyH, d.
    exact ((if d1 then true else false) :: ProdIntegrableSubsetRight I J hn x y d0).
Defined.

Lemma ProdIntegrableSubsetRight_length
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyH : Domain (ProdLFunc hn) (x,y)),
    length (ProdIntegrableSubsetRight hn x y xyH) = length hn.
Proof.
  induction hn.
  - reflexivity.
  - intros. simpl. destruct xyH, d. simpl.
    rewrite IHhn. reflexivity.
Qed.

(* Application of a list of rectangles, when none is activated. *)
Lemma ProdLFuncApplyZero
  : forall {I J : IntegrationSpace}
    (hn : list (@ProdIntegrable I J))
    (x : X (ElemFunc I)) (y : X (ElemFunc J))
    (xyS : Domain (ProdLFunc hn) (x,y)),
    (forall (n:nat) (ltnh : lt n (length hn)),
        partialApply _ _ (DomainProdLFuncInc hn x y xyS n ltnh) == 0)
    -> partialApply _ _ xyS == 0.
Proof.
  induction hn.
  - intros. reflexivity.
  - intros. destruct xyS.
    transitivity (partialApply _ _ d + partialApply _ _ d0).
    reflexivity. rewrite IHhn, CRplus_0_r. clear IHhn.
    assert (O < length (a :: hn))%nat.
    { apply le_n_S, le_0_n. }
    rewrite <- (H O H0). apply DomainProp.
    clear IHhn. intros.
    assert (S n < length (a :: hn))%nat.
    { apply le_n_S, ltnh. }
    rewrite <- (H (S n) H0). apply DomainProp.
Qed.

(* Application of a list of rectangles, when only one is activated. *)
Lemma ProdLFuncApplyUnique
  : forall {I J : IntegrationSpace}
    (hn : list (@ProdIntegrable I J))
    (x : X (ElemFunc I)) (y : X (ElemFunc J))
    (xyS : Domain (ProdLFunc hn) (x,y))
    (n : nat) (ltnh : lt n (length hn)),
    (forall (k:nat) (ltkh : lt k (length hn)),
        k <> n -> partialApply _ _ (DomainProdLFuncInc hn x y xyS k ltkh) == 0)
    -> partialApply _ _ xyS
      == partialApply _ _ (DomainProdLFuncInc hn x y xyS n ltnh).
Proof.
  induction hn.
  - intros. exfalso; inversion ltnh.
  - intros. destruct xyS. specialize (IHhn x y d0).
    transitivity (partialApply _ _ d + partialApply _ _ d0).
    reflexivity. destruct n.
    + simpl (nth 0 (a :: hn) (ProdIntegrableZero I J)).
      rewrite <- (CRplus_0_r (partialApply (ProdIntegrableFunc a) (x, y) (DomainProdLFuncInc (a :: hn) x y (d, d0) 0 ltnh))).
      apply CRplus_morph. apply DomainProp.
      apply ProdLFuncApplyZero. intros.
      assert (S n < length (a :: hn))%nat.
      { apply le_n_S, ltnh0. }
      rewrite <- (H (S n) H0). apply DomainProp. discriminate.
    + assert (n < length hn)%nat.
      { apply le_S_n. exact ltnh. }
      specialize (IHhn n H0). rewrite IHhn. clear IHhn.
      rewrite <- (CRplus_0_l (partialApply (ProdIntegrableFunc (nth (S n) (a :: hn) (ProdIntegrableZero I J)))
    (x, y) (DomainProdLFuncInc (a :: hn) x y (d, d0) (S n) ltnh))).
      apply CRplus_morph. 2: apply DomainProp.
      assert (0 < S (length hn))%nat. apply le_n_S, le_0_n.
      specialize (H O H1). unfold nth in H. rewrite <- H.
      apply DomainProp. discriminate. clear IHhn. intros.
      assert (S k < length (a :: hn))%nat.
      { apply le_n_S, ltkh. }
      specialize (H (S k) H2).
      simpl (nth (S k) (a :: hn) (ProdIntegrableZero I J)) in H.
      rewrite <- H. apply DomainProp. intro abs. inversion abs. contradiction.
Qed.

Lemma ProdIntegrableSubsetLeft_match
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyH : Domain (ProdLFunc hn) (x,y))
      (init : X (ElemFunc I) -> Prop),
    init x
    -> SubsetIntersectLeft hn init (ProdIntegrableSubsetLeft hn x y xyH) x.
Proof.
  induction hn.
  - intros. exact H.
  - intros. destruct xyH, d, d; split.
    exact p. apply IHhn. exact H.
    apply IHhn. exact H. exact n.
Qed.

Lemma ProdIntegrableSubsetRight_match
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyH : Domain (ProdLFunc hn) (x,y))
      (init : X (ElemFunc J) -> Prop),
    init y
    -> SubsetIntersectRight hn init (ProdIntegrableSubsetRight hn x y xyH) y.
Proof.
  induction hn.
  - intros. exact H.
  - intros. destruct xyH, d, d1; split.
    exact p. apply IHhn. exact H.
    apply IHhn. exact H. exact n.
Qed.

Lemma ApplyOutsidePointLeft
  : forall {I J : IntegrationSpace}
    (hn : list (@ProdIntegrable I J))
    (x : X (ElemFunc I)) (y : X (ElemFunc J))
    (xyH : Domain (ProdLFunc hn) (x,y)),
    Forall (fun fg : ProdIntegrable => ~ prodint_g fg y) hn
    -> SubsetIntersectFactor hn (ProdIntegrableSubsetLeft hn x y xyH)
                            (ProdIntegrableSubsetRight hn x y xyH) == 0.
Proof.
  induction hn.
  - reflexivity.
  - intros. inversion H. destruct xyH, d. specialize (IHhn x y d0 H3).
    subst x0. subst l. simpl. destruct d.
    + destruct d1. contradiction. simpl. rewrite IHhn.
      apply CRplus_0_l.
    + simpl. rewrite IHhn. apply CRplus_0_l.
Qed.

Lemma ApplyOutsidePointRight
  : forall {I J : IntegrationSpace}
    (hn : list (@ProdIntegrable I J))
    (x : X (ElemFunc I)) (y : X (ElemFunc J))
    (xyH : Domain (ProdLFunc hn) (x,y)),
    Forall (fun fg : ProdIntegrable => ~ prodint_f fg x) hn
    -> SubsetIntersectFactor hn (ProdIntegrableSubsetLeft hn x y xyH)
                            (ProdIntegrableSubsetRight hn x y xyH) == 0.
Proof.
  induction hn.
  - reflexivity.
  - intros. inversion H. destruct xyH, d. specialize (IHhn x y d0 H3).
    subst x0. subst l. simpl. destruct d.
    + destruct d1. contradiction. simpl. rewrite IHhn.
      apply CRplus_0_l.
    + simpl. rewrite IHhn. apply CRplus_0_l.
Qed.

Lemma list_prod_head : forall { A B : Type } (l : list A) (k : list B)
                         (a : A) (b : B),
    l <> nil -> k <> nil ->
    nth 0 (list_prod l k) (a,b)
    = (nth 0 l a, nth 0 k b).
Proof.
  intros. destruct l,k. reflexivity.
  contradiction. contradiction. reflexivity.
Qed.

Lemma ProdLFuncDomainLeft
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J)),
    Domain (ProdLFunc hn) (x,y)
    -> { n:nat | lt n (length hn) /\ prodint_f (nth n hn (ProdIntegrableZero I J)) x }
      + { forall n:nat, lt n (length hn) -> ~prodint_f (nth n hn (ProdIntegrableZero I J)) x }.
Proof.
  induction hn.
  - intros x y H. right. intros. exfalso. inversion H0.
  - intros x y H. destruct H, d. unfold fst in d. destruct d.
    + left. exists O. split. apply le_n_S, le_0_n. exact p.
    + specialize (IHhn x y d0) as [[k isin] | isout].
      left. exists (S k). destruct isin. split. apply le_n_S, H. exact H0.
      right. intros. destruct n0. exact n.
      apply isout. apply le_S_n, H.
Qed.

Lemma ProdLFuncDomainRight
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J)),
    Domain (ProdLFunc hn) (x,y)
    -> { n:nat | lt n (length hn) /\ prodint_g (nth n hn (ProdIntegrableZero I J)) y }
      + { forall n:nat, lt n (length hn) -> ~prodint_g (nth n hn (ProdIntegrableZero I J)) y }.
Proof.
  induction hn.
  - intros x y H. right. intros. exfalso. inversion H0.
  - intros x y H. destruct H, d. unfold snd in d1. destruct d1.
    + left. exists O. split. apply le_n_S, le_0_n. exact p.
    + specialize (IHhn x y d0) as [[k isin] | isout].
      left. exists (S k). destruct isin. split. apply le_n_S, H. exact H0.
      right. intros. destruct n0. exact n.
      apply isout. apply le_S_n, H.
Qed.

Fixpoint ConstFilter (b : bool) (n : nat) : list bool
  := match n with
     | O => nil
     | S p => b :: ConstFilter b p
     end.

Lemma ConstFilter_length : forall (b:bool) (n:nat),
    length (ConstFilter b n) = n.
Proof.
  induction n. reflexivity. simpl. apply f_equal, IHn.
Qed.

Lemma ConstFilter_false : forall {A : Set} (hn : list (A -> Prop)) (x : A)
                                 (init : A -> Prop),
    init x
    -> Forall (fun h => ~h x) hn
    -> SubsetIntersectFilter hn init (ConstFilter false (length hn)) x.
Proof.
  induction hn.
  - intros. exact H.
  - intros. inversion H0. split. 2: exact H3.
    exact (IHhn x init H H4).
Qed.

Lemma SubsetIntersectFilterOut
  : forall {A : Set}
      (hn : list (A -> Prop))
      (x : A),
    (forall filter : list bool,
        length filter = length hn
        -> ~SubsetIntersectFilter hn (SubsetUnion hn) filter x)
    -> Forall (fun h => ~h x) hn.
Proof.
  induction hn.
  - intros. apply Forall_nil.
  - intros.
    assert (a x
            -> forall filter : list bool,
               length filter = length hn ->
               ~ SubsetIntersectFilter hn (SubsetUnion (a :: hn)) filter x).
    { intros. intro abs. apply (H (true :: filter)).
      simpl. apply f_equal. exact H1. split. exact H0. exact abs. }
    assert (a x -> Forall (fun h => ~h x) hn).
    { intros. apply IHhn. intros. specialize (H0 H1 filter H2).
      intro abs. apply H0.
      apply (SubsetIntersectFilterInc hn (SubsetUnion hn) _ filter x).
      intros. right. exact H3. exact abs. }
    assert (~a x).
    { intro abs. apply (H0 abs (ConstFilter false (length hn))).
      specialize (H1 abs). apply ConstFilter_length.
      apply ConstFilter_false. left. exact abs. exact (H1 abs). }
    clear H0. clear H1. apply Forall_cons.
    + exact H2.
    + apply IHhn. intros. intro abs. apply (H (false :: filter)).
      simpl. apply f_equal, H0. split. 2: exact H2.
      apply (SubsetIntersectFilterInc hn (SubsetUnion hn) _ filter x).
      intros. right. exact H1. exact abs.
Qed.

Lemma DomainProdLFuncSplitCoord
  : forall {I J : IntegrationSpace}
      (hn : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J)),
    (forall n:nat, lt n (length hn)
                   -> { prodint_f (nth n hn (ProdIntegrableZero I J)) x }
                      + { ~prodint_f (nth n hn (ProdIntegrableZero I J)) x })
    -> (forall n:nat, lt n (length hn)
                   -> { prodint_g (nth n hn (ProdIntegrableZero I J)) y }
                      + { ~prodint_g (nth n hn (ProdIntegrableZero I J)) y })
    -> Domain (ProdLFunc hn) (x,y).
Proof.
  induction hn.
  - intros. simpl. trivial.
  - intros. split.
    + split. apply (H O). apply le_n_S, le_0_n.
      apply (H0 O). apply le_n_S, le_0_n.
    + apply IHhn.
      intros. apply le_n_S in H1. exact (H (S n) H1).
      intros. apply le_n_S in H1. exact (H0 (S n) H1).
Qed.

Lemma ProdIntegrableSimplifyDomain :
  forall {I J : IntegrationSpace}
    (hn : list (@ProdIntegrable I J))
    (x : X (ElemFunc I)) (y : X (ElemFunc J)),
    Domain (ProdLFunc (ProdIntegrableSimplify hn)) (x,y)
    -> Domain (ProdLFunc hn) (x,y).
Proof.
  intros I J hn x y H.
  assert (lt O (length (FreeSubsets (length hn)))) as flen.
  { destruct (FreeSubsets (length hn)) eqn:des. exfalso.
    exact (FreeSubsetsNotNil _ des). apply le_n_S, le_0_n. }
  apply DomainProdLFuncSplitCoord.
  - destruct (ProdLFuncDomainLeft _ x y H) as [[nl isinl] | H0].
    + intros. destruct isinl.
      unfold ProdIntegrableSimplify in H2.
      rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))) in H2.
      2: exact H1.
      unfold ProdIntegrableSimplify in H1. rewrite map_length, prod_length in H1.
      rewrite (map_nth (fun xy : list bool * list bool =>
                          ProdSubsetIntersect hn (fst xy) (snd xy))) in H2.
      simpl in H2. unfold SubsetIntersectLeft in H2.
      apply (DomainProdSubsetIntersect
               (map prodint_f hn) _ _ _ n) in H2.
      destruct (nth_error (map prodint_f hn) n) eqn:des.
      apply (nth_error_nth (map prodint_f hn) n
                           (prodint_f (ProdIntegrableZero I J))) in des.
      subst P.
      destruct (nth_error
                  (fst (nth nl (list_prod (FreeSubsets (length hn)) (FreeSubsets (length hn))) (nil, nil))) n)
               eqn:des2.
      destruct b. left. rewrite map_nth in H2. exact H2.
      rewrite map_nth in H2. right. exact H2.
      exfalso.
      apply nth_error_None in des2.
      rewrite nth_list_prod in des2. unfold fst in des2.
      rewrite (FreeSubsetsLength
                 (length hn) (nth (nl / length (FreeSubsets (length hn))) (FreeSubsets (length hn)) nil)) in des2.
      exact (lt_not_le _ _ H0 des2).
      apply nth_In.
      apply Nat.div_lt_upper_bound in H1. exact H1.
      intro abs. rewrite abs in flen. inversion flen. exact H1.
      exfalso. apply nth_error_None in des. rewrite map_length in des.
      exact (lt_not_le _ _ H0 des).
    + assert (Forall (fun h => ~h x) (map prodint_f hn)).
      { apply SubsetIntersectFilterOut. intros.
        destruct (FreeSubsetsFull filter) as [n [H2 H3]].
        specialize (H0 (n * (length (FreeSubsets (length hn))))%nat).
        rewrite map_length in H1. intro abs. apply H0.
        unfold ProdIntegrableSimplify. rewrite map_length, prod_length.
        rewrite <- Nat.mul_lt_mono_pos_r. rewrite <- H1. exact H2.
        exact flen. clear H0.
        unfold ProdIntegrableSimplify.
        rewrite (nth_indep _ (ProdIntegrableZero I J)
                           (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                                (snd (@nil bool, nil)))).
        rewrite (map_nth (fun xy : list bool * list bool =>
                            ProdSubsetIntersect hn (fst xy) (snd xy))).
        simpl. unfold SubsetIntersectLeft.
        rewrite (nth_list_prod (FreeSubsets (length hn)) (FreeSubsets (length hn))
                               nil nil (n * (length (FreeSubsets (length hn))))).
        unfold fst. rewrite Nat.div_mul. rewrite <- H1, H3. exact abs.
        intro H4. rewrite H4 in flen. inversion flen.
        rewrite <- Nat.mul_lt_mono_pos_r. rewrite <- H1. exact H2.
        exact flen. rewrite map_length, prod_length.
        rewrite <- Nat.mul_lt_mono_pos_r. rewrite <- H1. exact H2. exact flen. }
      intros. right. rewrite Forall_forall in H1.
      apply (H1 (prodint_f (nth n hn (ProdIntegrableZero I J)))).
      apply in_map, nth_In, H2.
  - destruct (ProdLFuncDomainRight _ x y H) as [[nl isinl] | H0].
    + intros. destruct isinl.
      unfold ProdIntegrableSimplify in H2.
      rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))) in H2.
      2: exact H1.
      unfold ProdIntegrableSimplify in H1. rewrite map_length, prod_length in H1.
      rewrite (map_nth (fun xy : list bool * list bool =>
                          ProdSubsetIntersect hn (fst xy) (snd xy))) in H2.
      simpl in H2. unfold SubsetIntersectLeft in H2.
      apply (DomainProdSubsetIntersect
               (map prodint_g hn) _ _ _ n) in H2.
      destruct (nth_error (map prodint_g hn) n) eqn:des.
      apply (nth_error_nth (map prodint_g hn) n
                           (prodint_g (ProdIntegrableZero I J))) in des.
      subst P.
      destruct (nth_error
                  (snd (nth nl (list_prod (FreeSubsets (length hn)) (FreeSubsets (length hn))) (nil, nil))) n)
               eqn:des2.
      destruct b. left. rewrite map_nth in H2. exact H2.
      rewrite map_nth in H2. right. exact H2.
      exfalso.
      apply nth_error_None in des2.
      rewrite nth_list_prod in des2. unfold snd in des2.
      rewrite (FreeSubsetsLength
                 (length hn) (nth (nl mod length (FreeSubsets (length hn))) (FreeSubsets (length hn)) nil)) in des2.
      exact (lt_not_le _ _ H0 des2).
      apply nth_In. apply Nat.mod_bound_pos. apply le_0_n.
      exact flen. exact H1.
      exfalso. apply nth_error_None in des. rewrite map_length in des.
      exact (lt_not_le _ _ H0 des).
    + assert (Forall (fun h => ~h y) (map prodint_g hn)).
      { apply SubsetIntersectFilterOut. intros.
        destruct (FreeSubsetsFull filter) as [n [H2 H3]].
        specialize (H0 n).
        rewrite map_length in H1. intro abs. apply H0.
        unfold ProdIntegrableSimplify. rewrite map_length, prod_length.
        apply (lt_le_trans _ (1 * length (FreeSubsets (length hn)))).
        rewrite Nat.mul_1_l. rewrite <- H1. exact H2.
        apply Nat.mul_le_mono_nonneg_r. apply le_0_n. exact flen.
        clear H0.
        unfold ProdIntegrableSimplify.
        rewrite (nth_indep _ (ProdIntegrableZero I J)
                           (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                                (snd (@nil bool, nil)))).
        rewrite (map_nth (fun xy : list bool * list bool =>
                            ProdSubsetIntersect hn (fst xy) (snd xy))).
        simpl. unfold SubsetIntersectRight.
        rewrite (nth_list_prod (FreeSubsets (length hn)) (FreeSubsets (length hn))
                               nil nil n).
        unfold snd. rewrite Nat.mod_small. rewrite <- H1, H3. exact abs.
        rewrite <- H1. exact H2.
        apply (lt_le_trans _ (1 * length (FreeSubsets (length hn)))).
        rewrite Nat.mul_1_l. rewrite <- H1. exact H2.
        apply Nat.mul_le_mono_nonneg_r. apply le_0_n. exact flen.
        rewrite map_length, prod_length.
        apply (lt_le_trans _ (1 * length (FreeSubsets (length hn)))).
        rewrite Nat.mul_1_l. rewrite <- H1. exact H2.
        apply Nat.mul_le_mono_nonneg_r. apply le_0_n. exact flen. }
      intros. right. rewrite Forall_forall in H1.
      apply (H1 (prodint_g (nth n hn (ProdIntegrableZero I J)))).
      apply in_map, nth_In, H2.
Qed.

Lemma ProdIntegrableSimplifyApply :
  forall {I J : IntegrationSpace}
    (hn : list (@ProdIntegrable I J))
    (x : X (ElemFunc I)) (y : X (ElemFunc J))
    (xyH : Domain (ProdLFunc hn) (x,y))
    (xyS : Domain (ProdLFunc (ProdIntegrableSimplify hn)) (x,y)),
    partialApply _ _ xyS
    == SubsetIntersectFactor
         hn (ProdIntegrableSubsetLeft hn x y xyH)
         (ProdIntegrableSubsetRight hn x y xyH).
Proof.
  intros. destruct (SubsetUnionLeftDec hn x y xyH) as [inunionf|notinunionf].
  destruct (SubsetUnionRightDec hn x y xyH) as [inuniong|notinuniong].
  pose proof (FreeSubsetsFull (ProdIntegrableSubsetLeft hn x y xyH)) as [kf H].
  rewrite ProdIntegrableSubsetLeft_length in H.
  pose proof (FreeSubsetsFull (ProdIntegrableSubsetRight hn x y xyH)) as [kg H0].
  rewrite ProdIntegrableSubsetRight_length in H0.
  assert (kg + kf * (length (FreeSubsets (length hn)))
          < length (ProdIntegrableSimplify hn))%nat.
  { unfold ProdIntegrableSimplify. rewrite map_length, prod_length.
    destruct H.
    apply (lt_le_trans _ (length (FreeSubsets (length hn))
                          + kf * length (FreeSubsets (length hn)))).
    rewrite <- Nat.add_lt_mono_r. apply H0.
    apply (Nat.mul_le_mono_nonneg_r (S kf) _ (length (FreeSubsets (length hn)))).
    apply le_0_n. exact H. }
  rewrite (ProdLFuncApplyUnique
             (ProdIntegrableSimplify hn) x y xyS
             (kg + kf * (length (FreeSubsets (length hn)))) H1).
  - (* single matching point *)
    assert (kg + kf * (length (FreeSubsets (length hn)))
            < length (FreeSubsets (length hn)) * length (FreeSubsets (length hn)))%nat.
    { unfold ProdIntegrableSimplify in H1
      ; rewrite map_length, prod_length in H1. exact H1. }
    pose proof (nth_list_prod
                  (FreeSubsets (length hn)) (FreeSubsets (length hn)) nil nil
                  (kg + kf * (length (FreeSubsets (length hn)))) H2).
    rewrite Nat.div_add, Nat.mod_add, Nat.div_small, Nat.mod_small in H3.
    2: apply H0. 2: apply H0.
    symmetry. rewrite <- CRmult_1_r.
    apply CRmult_morph. rewrite <- CRmult_1_r.
    apply CRmult_morph.
    + unfold ProdIntegrableSimplify.
      rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))).
      rewrite (map_nth (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))), H3.
      unfold fst, snd. destruct H, H0. simpl (0 + kf)%nat.
      rewrite H4, H5. reflexivity.
      rewrite map_length. rewrite prod_length. exact H2.
    + destruct (DomainProdLFuncInc (ProdIntegrableSimplify hn) x y xyS
                                   (kg + kf * length (FreeSubsets (length hn))) H1).
      destruct d. reflexivity. exfalso. simpl in n. apply n.
      unfold ProdIntegrableSimplify.
      rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))).
      rewrite (map_nth (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))), H3.
      simpl. destruct H. rewrite H4.
      apply ProdIntegrableSubsetLeft_match. apply inunionf. exact H1.
    + destruct (DomainProdLFuncInc (ProdIntegrableSimplify hn) x y xyS
                                   (kg + kf * length (FreeSubsets (length hn))) H1).
      destruct d0. reflexivity. exfalso. simpl in n. apply n.
      unfold ProdIntegrableSimplify.
      rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))).
      rewrite (map_nth (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))), H3.
      simpl. destruct H0. rewrite H4.
      apply ProdIntegrableSubsetRight_match. apply inuniong. exact H1.
    + intros abs. destruct H. rewrite abs in H. inversion H.
    + intros abs. destruct H. rewrite abs in H. inversion H.
  - (* Other points evaluate to zero *)
    intros. simpl.
    rewrite CRmult_assoc. rewrite (CRmult_morph _ _ _ (CReq_refl _) _ 0).
    apply CRmult_0_r.
    destruct (DomainProdLFuncInc (ProdIntegrableSimplify hn) x y xyS k ltkh).
    destruct d. destruct d0.
    2: unfold snd; apply CRmult_0_r.
    2: unfold fst; apply CRmult_0_l. exfalso.
    assert (k < length (FreeSubsets (length hn)) * length (FreeSubsets (length hn)))%nat.
    { unfold ProdIntegrableSimplify in ltkh.
      rewrite map_length, prod_length in ltkh. exact ltkh. }
    pose proof (nth_list_prod
                  (FreeSubsets (length hn)) (FreeSubsets (length hn)) nil nil
                  k H3).
    unfold fst, ProdIntegrableSimplify in p.
    rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))) in p.
    rewrite (map_nth (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))), H4 in p.
    unfold fst, snd in p.
    unfold fst, ProdIntegrableSimplify in p0.
    rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))) in p0.
    rewrite (map_nth (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))), H4 in p0.
    unfold fst, snd in p0.
    2: rewrite map_length, prod_length; exact H3.
    2: rewrite map_length, prod_length; exact H3.
    clear H4.
    assert (0 < length (FreeSubsets (length hn)))%nat as lenPos.
    { apply (le_lt_trans _ kg _ (le_0_n _)). apply H0. }
    destruct (Nat.eq_dec (k / length (FreeSubsets (length hn))) kf).
    + rewrite e in p0. clear p. simpl in p0.
      apply (ProdIntegrableSubsetsDisjoint
               (map prodint_g hn)
               (nth (k mod length (FreeSubsets (length hn))) (FreeSubsets (length hn)) nil)
               (ProdIntegrableSubsetRight hn x y xyH) y).
      rewrite ProdIntegrableSubsetRight_length.
      apply FreeSubsetsLength. apply nth_In.
      apply Nat.mod_bound_pos. apply le_0_n. exact lenPos.
      apply FreeSubsetsLength. rewrite map_length. apply nth_In.
      apply Nat.mod_bound_pos. apply le_0_n. exact lenPos.
      destruct H0. rewrite <- H4.
      apply FreeSubsetsDifferent. intro abs. subst kg. subst kf.
      pose proof (Nat.div_mod k (length (FreeSubsets (length hn)))).
      rewrite Nat.add_comm, Nat.mul_comm in H5. apply H2, H5.
      intro abs. rewrite abs in lenPos. inversion lenPos.
      apply Nat.mod_bound_pos. apply le_0_n. exact lenPos.
      exact H0. split. exact p0.
      apply ProdIntegrableSubsetRight_match. apply inuniong.
    + clear p0. simpl in p.
      assert (k / length (FreeSubsets (length hn)) < length (FreeSubsets (length hn)))%nat.
      { apply Nat.div_lt_upper_bound in H3. exact H3.
        intro abs. rewrite abs in lenPos. inversion lenPos. }
      apply (ProdIntegrableSubsetsDisjoint
               (map prodint_f hn)
               (nth (k / length (FreeSubsets (length hn))) (FreeSubsets (length hn)) nil)
               (ProdIntegrableSubsetLeft hn x y xyH) x).
      rewrite ProdIntegrableSubsetLeft_length.
      apply FreeSubsetsLength. apply nth_In. exact H4.
      apply FreeSubsetsLength. rewrite map_length. apply nth_In. exact H4.
      destruct H. rewrite <- H5.
      apply FreeSubsetsDifferent. exact n. exact H4. exact H.
      split. exact p. apply ProdIntegrableSubsetLeft_match. apply inunionf.
  - (* If y is in no subsets, then 0 == 0. *)
    rewrite ApplyOutsidePointLeft. 2: apply notinuniong.
    apply ProdLFuncApplyZero. intros. simpl.
    destruct (DomainProdLFuncInc
                (ProdIntegrableSimplify hn) x y xyS n ltnh), d0.
    2: apply CRmult_0_r. exfalso. clear d. simpl in p.
    unfold ProdIntegrableSimplify in p.
    rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))) in p.
    2: exact ltnh.
    rewrite (map_nth (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))),
      nth_list_prod in p.
    unfold fst, snd in p. apply SubsetIntersectFilter_init in p.
    destruct (SubsetUnionRightDec hn x y xyH).
    destruct H, notinuniong. contradiction.
    destruct H, notinuniong. contradiction.
    unfold ProdIntegrableSimplify in ltnh.
    rewrite map_length, prod_length in ltnh. exact ltnh.
  - (* If x is in no subsets, then 0 == 0. *)
    rewrite ApplyOutsidePointRight. 2: apply notinunionf.
    apply ProdLFuncApplyZero. intros. simpl.
    destruct (DomainProdLFuncInc
                (ProdIntegrableSimplify hn) x y xyS n ltnh), d.
    2: rewrite CRmult_0_r; apply CRmult_0_l.
    exfalso. clear d0. simpl in p.
    unfold ProdIntegrableSimplify in p.
    rewrite (nth_indep _ (ProdIntegrableZero I J)
                         (ProdSubsetIntersect hn (fst (nil,@nil bool))
                                              (snd (@nil bool, nil)))) in p.
    2: exact ltnh.
    rewrite (map_nth (fun xy => ProdSubsetIntersect hn (fst xy) (snd xy))),
      nth_list_prod in p.
    unfold fst, snd in p. apply SubsetIntersectFilter_init in p.
    destruct (SubsetUnionLeftDec hn x y xyH).
    destruct H, notinunionf. contradiction.
    destruct H, notinunionf. contradiction.
    unfold ProdIntegrableSimplify in ltnh.
    rewrite map_length, prod_length in ltnh. exact ltnh.
Qed.

Lemma ApplyIntersectFactor :
  forall {I J : IntegrationSpace}
    (hn : list (@ProdIntegrable I J))
    (x : X (ElemFunc I)) (y : X (ElemFunc J))
    (xyH : Domain (ProdLFunc hn) (x,y)),
    partialApply (ProdLFunc hn) (x, y) xyH ==
    SubsetIntersectFactor hn (ProdIntegrableSubsetLeft hn x y xyH)
                          (ProdIntegrableSubsetRight hn x y xyH).
Proof.
  induction hn.
  - reflexivity.
  - intros. destruct xyH. specialize (IHhn x y d0).
    simpl. rewrite IHhn. clear IHhn. destruct d. simpl.
    rewrite CRplus_comm.
    apply CRplus_morph. reflexivity. destruct d.
    destruct d1. do 2 rewrite CRmult_1_r. reflexivity.
    rewrite CRmult_1_r. rewrite CRmult_0_r. reflexivity.
    destruct d1. rewrite CRmult_0_r, CRmult_0_l. reflexivity.
    rewrite CRmult_0_r. reflexivity.
Qed.

Lemma ProdIntegrableSimplifyEq :
  forall {I J : IntegrationSpace}
    (hn : list (@ProdIntegrable I J))
    (x : X (ElemFunc I)) (y : X (ElemFunc J))
    (xyH : Domain (ProdLFunc hn) (x,y))
    (xyS : Domain (ProdLFunc (ProdIntegrableSimplify hn)) (x,y)),
  partialApply _ _ xyH == partialApply _ _ xyS.
Proof.
  (* ProdLFunc hn is the linear combination of hn, so we know
     whether x and y belong to each of the components of hn.
     That makes a subset which selects only one component of
     ProdIntegrableSimplify hn.
     The value on that component is SubsetIntersectFactor which
     sums all the activated coefficients, as ProdLFunc hn does. *)
  intros. rewrite (ProdIntegrableSimplifyApply hn x y xyH).
  apply ApplyIntersectFactor.
Qed.

Definition ProdIntegrableMapCoef
           {I J : IntegrationSpace}
  : (CRcarrier (RealT (ElemFunc I)) -> CRcarrier (RealT (ElemFunc I)))
    -> @ProdIntegrable I J -> @ProdIntegrable I J
  := fun f P => Build_ProdIntegrable
                  I J
                  (prodint_f P) (prodint_g P)
                  (f (prodint_factor P))
                  (prodint_fint P) (prodint_gint P).

Lemma DomainProdLFuncMap
  : forall {I J : IntegrationSpace}
      (l : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (f : CRcarrier (RealT (ElemFunc I)) -> CRcarrier (RealT (ElemFunc I))),
    Domain (ProdLFunc (map (ProdIntegrableMapCoef f) l)) (x,y)
    -> Domain (ProdLFunc l) (x, y).
Proof.
  induction l.
  - intros. simpl. trivial.
  - intros x y f H. destruct H. split.
    + destruct a; split; apply d.
    + exact (IHl x y f d0).
Qed.

Lemma ApplyProdLFuncDisjointHead
  : forall {I J : IntegrationSpace}
      (l : list ProdIntegrable)
      (a : @ProdIntegrable I J)
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyL : Domain (ProdLFunc l) (x,y)),
    ProdIntegrableSimple (a :: l)
    -> prodint_f a x
    -> prodint_g a y
    -> partialApply _ (x,y) xyL == 0.
Proof.
  induction l.
  - intros. reflexivity.
  - intros. simpl. destruct xyL, d. simpl.
    assert (ProdIntegrableSimple (a0 :: l)) as simple0.
    { destruct H, H. split. exact H. inversion H2. exact H7. }
    destruct d.
    + destruct d1. exfalso.
      simpl in p, p0. destruct H. inversion H2.
      apply (H5 x y). repeat split; assumption.
      rewrite CRmult_0_r, CRplus_0_l.
      apply (IHl a0). exact simple0. exact H0. exact H1.
    + rewrite CRmult_0_r, CRmult_0_l, CRplus_0_l.
      apply (IHl a0). exact simple0. exact H0. exact H1.
Qed.

Lemma ApplyProdLFuncDisjointHeadMap
  : forall {I J : IntegrationSpace}
      (l : list ProdIntegrable)
      (a : @ProdIntegrable I J)
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (f : CRcarrier (RealT (ElemFunc I)) -> CRcarrier (RealT (ElemFunc I)))
      (xyL : Domain (ProdLFunc (map (ProdIntegrableMapCoef f) l)) (x,y)),
    ProdIntegrableSimple (a :: l)
    -> prodint_f a x
    -> prodint_g a y
    -> partialApply _ (x,y) xyL == 0.
Proof.
  induction l.
  - intros. reflexivity.
  - intros. simpl. destruct xyL, d. simpl.
    assert (ProdIntegrableSimple (a0 :: l)) as simple0.
    { destruct H, H. split. exact H. inversion H2. exact H7. }
    destruct d.
    + destruct d1. exfalso.
      simpl in p, p0. destruct H. inversion H2.
      apply (H5 x y). repeat split; assumption.
      rewrite CRmult_0_r, CRplus_0_l.
      apply (IHl a0). exact simple0. exact H0. exact H1.
    + rewrite CRmult_0_r, CRmult_0_l, CRplus_0_l.
      apply (IHl a0). exact simple0. exact H0. exact H1.
Qed.

(* When a list of rectangles is disjoint, a point (x,y)
   is inside at most one rectangle. The sum reduces to one coefficient. *)
Lemma ApplyProdLFuncDisjointAbs
  : forall {I J : IntegrationSpace}
      (l : list (@ProdIntegrable I J))
      (x : X (ElemFunc I)) (y : X (ElemFunc J))
      (xyL : Domain (ProdLFunc l) (x,y))
      (f : CRcarrier (RealT (ElemFunc I)) -> CRcarrier (RealT (ElemFunc I)))
      (xyA : Domain (ProdLFunc (map (ProdIntegrableMapCoef f) l)) (x,y)),
    ProdIntegrableSimple l
    -> f 0 == 0
    -> (forall x y : CRcarrier (RealT (ElemFunc I)),
          x == y -> f x == f y)
    -> partialApply (ProdLFunc (map (ProdIntegrableMapCoef f) l)) (x,y) xyA
       == f (partialApply (ProdLFunc l) (x,y) xyL).
Proof.
  induction l as [|a l].
  - intros. rewrite H0. reflexivity.
  - intros. simpl. destruct xyA, xyL, d.
    unfold fst in d. destruct d. unfold snd in d3.
    destruct d3.
    + (* (x,y) is inside a, stop the sum there. *)
      simpl.
      rewrite (H1 (prodint_factor a * (if fst d1 then 1 else 0) * (if snd d1 then 1 else 0) +
     partialApply
       (fold_right Xplus (Xconst (X (ElemFunc I) * X (ElemFunc J)) 0)
          (map ProdIntegrableFunc l)) (x, y) d2)
                  (prodint_factor a)).
      rewrite (ApplyProdLFuncDisjointHeadMap l a x y f d0 H p p0).
      rewrite CRplus_0_r. do 2 rewrite CRmult_1_r. reflexivity.
      destruct d1. simpl.
      destruct d. destruct d1.
      2: contradiction. 2: contradiction.
      do 2 rewrite CRmult_1_r.
      rewrite (ApplyProdLFuncDisjointHead l a x y d2 H p p0).
      rewrite CRplus_0_r. reflexivity.
    + (* (x,y) is outside a, use induction hypothesis. *)
      simpl. rewrite CRmult_0_r, CRplus_0_l.
      rewrite (H1 (prodint_factor a * (if fst d1 then 1 else 0) * (if snd d1 then 1 else 0) +
     partialApply
       (fold_right Xplus (Xconst (X (ElemFunc I) * X (ElemFunc J)) 0)
          (map ProdIntegrableFunc l)) (x, y) d2)
                  (partialApply (ProdLFunc l) (x, y) d2)).
      apply IHl. apply H. exact H0. exact H1.
      destruct d1. unfold snd in d1. simpl.
      destruct d. destruct d1. contradiction.
      rewrite CRmult_0_r, CRplus_0_l. reflexivity.
      rewrite CRmult_0_r, CRmult_0_l, CRplus_0_l. reflexivity.
    + (* (x,y) is outside a, use induction hypothesis. *)
      simpl. rewrite CRmult_0_r, CRmult_0_l, CRplus_0_l.
      destruct d1. simpl.
      rewrite (H1 (prodint_factor a * (if d then 1 else 0) * (if d1 then 1 else 0) +
     partialApply
       (fold_right Xplus (Xconst (X (ElemFunc I) * X (ElemFunc J)) 0)
          (map ProdIntegrableFunc l)) (x, y) d2)
                  (partialApply (ProdLFunc l) (x, y) d2)).
      apply IHl. apply H. exact H0. exact H1.
      destruct d. destruct d1. contradiction.
      rewrite CRmult_0_r, CRplus_0_l. reflexivity.
      rewrite CRmult_0_r, CRmult_0_l, CRplus_0_l. reflexivity.
Qed.

Lemma ApplyMapCoef :
  forall {I J : IntegrationSpace} (a : CRcarrier (RealT (ElemFunc I)))
    (l : list ProdIntegrable)
    (x : X (ElemFunc I)) (y : X (ElemFunc J))
    (xyDS : Domain (ProdLFunc (map (ProdIntegrableMapCoef (fun x0 : CRcarrier _ => a * x0)) l)) (x,y)),
  partialApply _ (x, y) xyDS
  == a * partialApply (ProdLFunc l) (x, y) (DomainProdLFuncMap l x y (fun x0 : CRcarrier _ => a * x0) xyDS).
Proof.
  induction l.
  - intros. simpl. rewrite CRmult_0_r. reflexivity.
  - intros. simpl. destruct xyDS. rewrite IHl.
    destruct (DomainProdLFuncMap (a0 :: l) x y (fun x0 : CRcarrier _ => a * x0) (d, d0)).
    rewrite CRmult_assoc, CRmult_assoc, <- CRmult_plus_distr_l.
    apply CRmult_morph. reflexivity.
    apply CRplus_morph. 2: apply DomainProp.
    destruct d, d1. simpl. destruct d. destruct d1. 2: contradiction.
    destruct d3. destruct d4. 2: contradiction.
    rewrite CRmult_assoc. reflexivity.
    destruct d4. contradiction. rewrite CRmult_assoc. reflexivity.
    rewrite CRmult_0_l. destruct d1. contradiction.
    rewrite CRmult_0_r, CRmult_0_l. reflexivity.
Qed.

Lemma ProductMinConstStable
  : forall {I J : IntegrationSpace}
      (l : list (@ProdIntegrable I J))
      (a : CRcarrier (RealT (ElemFunc I))) (aPos : 0 < a),
    PartialRestriction (ProdLFunc (map (ProdIntegrableMapCoef (fun x => CRmin x a)) (ProdIntegrableSimplify l)))
                       (XminConst (ProdLFunc l) a).
Proof.
  intros I J l.
  split.
  - intros [x y] H.
    apply DomainProdLFuncMap, ProdIntegrableSimplifyDomain in H. exact H.
  - intros [x y] xyDS xG. simpl.
    rewrite (ApplyProdLFuncDisjointAbs
               _ x y (DomainProdLFuncMap
                        (ProdIntegrableSimplify l) x y (fun x => CRmin x a) xyDS)).
    2: apply ProdIntegrableSimplifyDisjoint.
    apply CRmin_morph.
    rewrite <- (ProdIntegrableSimplifyEq
                 l x y (ProdIntegrableSimplifyDomain
                          l x y (DomainProdLFuncMap (ProdIntegrableSimplify l) x y
                                                    (fun x => CRmin x a) xyDS))).
    apply DomainProp. reflexivity.
    rewrite CRmin_left. reflexivity.
    apply CRlt_asym, aPos.
    intros. rewrite H. reflexivity.
Qed.

(* Product L-functions are linear combinations of products
   of integrable functions. *)
Definition ProductFunctionRieszSpace (I J : IntegrationSpace)
  : FunctionRieszSpace.
Proof.
  apply (Build_FunctionRieszSpace
           (prod (X (ElemFunc I)) (X (ElemFunc J)))
           (RealT (ElemFunc I))
           (* L-functions are functions that extend ProdLFunc.
              l empty means f is the zero function defined on
              the whole product space. *)
           (fun f => { l : list ProdIntegrable
                        & PartialRestriction (ProdLFunc l) f })).
  - (* extensionality of L *)
    intros f g H [l res]. exists l.
    apply (PartialRestriction_trans _ _ f _ res). destruct H.
    split. apply p. exact c.
  - (* stability under addition *)
    intros f g [l lf] [l0 lf0]. exists (l ++ l0).
    intros. split. intros [x y] xD. split.
    apply DomainProdLFuncAppLeft in xD. apply lf, xD.
    apply DomainProdLFuncAppRight in xD. apply lf0, xD.
    intros. destruct x as [x y].
    rewrite (ApplyProdLFuncApp
               l l0 x y (DomainProdLFuncAppLeft l l0 x y xD)
               (DomainProdLFuncAppRight l l0 x y xD) ).
    simpl. destruct xG. apply CRplus_morph. apply lf. apply lf0.
  - (* Stability under absolute value. Cut the domain into
       disjoint rectangles and apply the absolute value on each coefficient. *)
    intros f [l lf].
    exists (map (ProdIntegrableMapCoef (CRabs _)) (ProdIntegrableSimplify l)).
    split. intros [x y] H. destruct lf. apply d.
    exact (ProdIntegrableSimplifyDomain
             l x y (DomainProdLFuncMap
                      (ProdIntegrableSimplify l) x y (CRabs _) H)).
    intros [x y] xyDS xG. simpl.
    rewrite (ApplyProdLFuncDisjointAbs
               _ x y (DomainProdLFuncMap
                        (ProdIntegrableSimplify l) x y (CRabs _) xyDS)).
    2: apply ProdIntegrableSimplifyDisjoint.
    apply CRabs_morph.
    rewrite <- (ProdIntegrableSimplifyEq
                 l x y (ProdIntegrableSimplifyDomain
                          l x y (DomainProdLFuncMap
                                   (ProdIntegrableSimplify l) x y (CRabs _) xyDS))).
    apply lf.
    rewrite CRabs_right. reflexivity. apply CRle_refl.
    exact CRabs_morph.
  - (* Stability under minimum. Cut the domain into
       disjoint rectangles and apply the absolute value on each coefficient. *)
    intros f [l lf].
    exists (map (ProdIntegrableMapCoef (fun x => CRmin x 1)) (ProdIntegrableSimplify l)).
    apply (PartialRestriction_trans _ _ _ _ (ProductMinConstStable l 1 (CRzero_lt_one _))).
    split. intros [x y] H. destruct lf. apply d. exact H.
    intros [x y] xyDS xG. unfold XminConst, Xop, partialApply.
    destruct lf.
    rewrite (c _ xyDS xG). reflexivity.
  - (* stability under scaling *)
    intros a f [l H].
    exists (map (ProdIntegrableMapCoef (fun x => a * x)) l).
    split. intros [x y] H0. simpl. destruct H. apply d.
    exact (DomainProdLFuncMap l x y (fun x => a * x) H0).
    intros [x y] xyDS xyD.
    simpl. destruct H. rewrite ApplyMapCoef.
    apply CRmult_morph. reflexivity.
    apply (c (x,y) (DomainProdLFuncMap l x y (fun x => a * x) xyDS)).
Defined.

Definition IElemProduct { I J : IntegrationSpace }
           (f : PartialFunction (prod (X (ElemFunc I)) (X (ElemFunc J))))
  : L (ProductFunctionRieszSpace I J) f -> CRcarrier (RealT (ElemFunc I))
  := fun fL => let (l,_) := fL in
            fold_right (CRplus (RealT (ElemFunc I))) 0
                      (map (fun pi => prodint_factor pi
                                   * MeasureSet (prodint_fint pi)
                                   * CRcast (MeasureSet (prodint_gint pi)))
                           l).

Definition IntegrableFunctionAE
           { I J : IntegrationSpace }
           (f : @PartialFunction (RealT (ElemFunc I))
                                 (prod (X (ElemFunc I)) (X (ElemFunc J))))
  : Type
  := almost_everywhere (fun x : X (ElemFunc I)
                                  (* Shorter than casting the function and
                                     then casting back the integral. *)
                        => @IntegrableFunction (IntegrationSpaceCast J)
                                               (Xproj1 f x)).

Definition IntegralFst
           { I J : IntegrationSpace }
           (f : @PartialFunction (RealT (ElemFunc I))
                                 (prod (X (ElemFunc I)) (X (ElemFunc J))))
           (fInt : IntegrableFunctionAE f)
  : @PartialFunction (RealT (ElemFunc I)) (X (ElemFunc I)).
Proof.
  destruct fInt as [h [hint p]].
  apply (Build_PartialFunctionXY
           (X (ElemFunc I)) (CRcarrier (RealT (ElemFunc I))) (CReq _) (Domain h)
           (fun x xD => Integral (p x xD))).
  intros. apply (@IntegralExtensional (IntegrationSpaceCast J)).
  intros. apply DomainProp.
Defined.

Lemma SumProdIntFIntegrable
  : forall { I J : IntegrationSpace }
      (l : list (@ProdIntegrable I J)),
    IntegrableFunction
      (XsumList (map (fun x : ProdIntegrable => CharacFunc (prodint_f x)) l)).
Proof.
  induction l.
  - simpl. apply IntegrableZero.
  - simpl. apply IntegrablePlus. apply a. apply IHl.
Qed.

Lemma Xproj1Restriction
  : forall { I J : IntegrationSpace }
      (f g : @PartialFunction (RealT (ElemFunc I)) (prod (X (ElemFunc I)) (X (ElemFunc J))))
      (x : X (ElemFunc I)),
    PartialRestriction f g
    -> PartialRestriction (Xproj1 f x) (Xproj1 g x).
Proof.
  split.
  - intros y H. destruct X. exact (d (x,y) H).
  - intros. apply X.
Qed.

Lemma LElemProductIntegrableAEspec
  : forall { I J : IntegrationSpace }
      (l : list (@ProdIntegrable I J)) (x : X (ElemFunc I)),
    Domain (XsumList (map (fun pi => @CharacFunc (RealT (ElemFunc I)) _ (prodint_f pi)) l)) x
    -> @IntegrableFunction (IntegrationSpaceCast J) (Xproj1 (ProdLFunc l) x).
Proof.
  intros I J l x xDS.
  (* x in the domain of sum_i f_i.
     Xproj1 f x = sum_i (a_i f_i(x) g_i), integrable as a linear combination
     of integrable functions. *)
  induction l.
  - apply (IntegrableFunctionExtensional (Xconst _ 0)).
    split. intros y H0. simpl. trivial.
    intros. apply DomainProp. apply IntegrableZero.
  - unfold ProdLFunc. simpl.
    apply (@IntegrableFunctionExtensional
             (IntegrationSpaceCast J)
             (Xplus (Xproj1 (ProdIntegrableFunc a) x)
                    (Xproj1 (XsumList (map ProdIntegrableFunc l)) x))).
    split. intros y H0. apply H0.
    intros. destruct xD, xG. apply CRplus_morph.
    apply CRmult_morph. apply CRmult_morph. reflexivity.
    apply DomainProp. apply DomainProp. simpl. apply DomainProp.
    apply (@IntegrablePlus (IntegrationSpaceCast J)).
    2: apply IHl, xDS. destruct xDS.
    apply (@IntegrableFunctionExtensional
             (IntegrationSpaceCast J)
             (Xscale (prodint_factor a * partialApply _ x d)
                     (CharacFunc (prodint_g a)))).
    split. intros y H. split. exact d. exact H.
    intros. apply CRmult_morph. apply CRmult_morph.
    reflexivity. apply DomainProp. apply DomainProp.
    apply (@IntegrableScale (IntegrationSpaceCast J)).
    apply (@IntegrableFunctionExtensional
             (IntegrationSpaceCast J)
             (@PartialFunctionCast (RealT (ElemFunc J)) (RealT (ElemFunc I))
                                   _ (CharacFunc (prodint_g a)))).
    split. intros y ydf. exact ydf. intros. simpl.
    destruct xD, xG. apply CRmorph_one.
    contradiction. contradiction. apply CRmorph_zero.
    exact (@IntegrableFunctionCast
             J _ (CharacFunc (prodint_g a)) (prodint_gint a)).
Qed.

Lemma LElemProductIntegrableAE
  : forall { I J : IntegrationSpace }
      (l : list (@ProdIntegrable I J)),
    IntegrableFunctionAE (ProdLFunc l).
Proof.
  intros I J l.
  exists (XsumList (map (fun x => CharacFunc (prodint_f x)) l)). split.
  - apply SumProdIntFIntegrable.
  - apply LElemProductIntegrableAEspec.
Defined.

Definition ProdIntegrableFuncIntegrableAE
  : forall { I J : IntegrationSpace }
      (p : @ProdIntegrable I J),
    IntegrableFunctionAE (ProdIntegrableFunc p).
Proof.
  (* Maybe redundant. *)
  intros. exists (CharacFunc (prodint_f p)).
  split. apply p.
  intros x xD.
  apply (@IntegrableFunctionExtensional
           (IntegrationSpaceCast J)
           (Xscale (prodint_factor p * partialApply _ x xD)
                   (CharacFunc (prodint_g p)))).
  split. intros y H. split. exact xD. exact H.
  intros. apply CRmult_morph. apply CRmult_morph.
  reflexivity. apply DomainProp. apply DomainProp.
  apply (@IntegrableScale (IntegrationSpaceCast J)).
  apply (@IntegrableFunctionExtensional
           (IntegrationSpaceCast J)
           (@PartialFunctionCast (RealT (ElemFunc J)) (RealT (ElemFunc I))
                                 _ (CharacFunc (prodint_g p)))).
  split. intros y ydf. exact ydf. intros. simpl.
  destruct xD0, xG. apply CRmorph_one.
  contradiction. contradiction. apply CRmorph_zero.
  exact (@IntegrableFunctionCast
           J _ (CharacFunc (prodint_g p)) (prodint_gint p)).
Defined.

Lemma ProdIntegrableFuncIntegrable
  : forall {I J : IntegrationSpace }
      (a : ProdIntegrable),
  IntegrableFunction (IntegralFst (ProdIntegrableFunc a) (@ProdIntegrableFuncIntegrableAE I J a)).
Proof.
  intros.
  apply (IntegrableFunctionExtensional
           (Xscale (prodint_factor a * CRcast (Integral (prodint_gint a)))
                   (CharacFunc (prodint_f a)))).
  2: apply IntegrableScale, a. split.
  intros x xD. exact xD.
  intros. simpl in xD, xG.
  unfold ProdIntegrableFuncIntegrableAE, IntegralFst, partialApply;
    rewrite IntegralRestrict.
  rewrite (@IntegralScale (IntegrationSpaceCast J)),
  IntegralRestrict, IntegralFunctionCast.
  simpl.
  destruct xD. destruct xG. 2: contradiction.
  do 2 rewrite CRmult_1_r. rewrite CRmult_comm. reflexivity.
  destruct xG. contradiction.
  do 3 rewrite CRmult_0_r. reflexivity.
Defined.

Lemma LElemProductIntegralFstIntegrable
  : forall { I J : IntegrationSpace }
      (l : list (@ProdIntegrable I J)),
    IntegrableFunction (IntegralFst (ProdLFunc l) (LElemProductIntegrableAE l)).
Proof.
  (* Linear combination of integrable functions. *)
  induction l.
  - (* The zero function defined almost everywhere is integrable. *)
    unfold IntegralFst; destruct (LElemProductIntegrableAE nil) as [f p], p.
    apply (IntegrableFunctionExtensional (Xscale 0 f)).
    split. intros x H; exact H.
    intros; unfold Domain in xG. simpl.
    rewrite CRmult_0_l.
    rewrite (IntegralExtensional _ _ (i0 x xG) IntegrableZero).
    symmetry. apply (@IntegralZeroIsZero (IntegrationSpaceCast J)).
    intros. reflexivity.
    apply IntegrableScale, i.
  - apply (IntegrableFunctionExtensional
             (Xplus (IntegralFst _ (ProdIntegrableFuncIntegrableAE a))
                    (IntegralFst (ProdLFunc l) (LElemProductIntegrableAE l)))).
    split.
    + unfold IntegralFst. unfold LElemProductIntegrableAE.
      intros x [d d0]; unfold Domain in d0; simpl in d; split.
      exact d. exact d0.
    + intros.
      unfold IntegralFst.
      unfold LElemProductIntegrableAE, Xplus, XbinOp, XbinOpXY, partialApply.
      destruct xD.
      unfold ProdIntegrableFuncIntegrableAE;
      rewrite IntegralRestrict.
      rewrite <- (@IntegralPlus (IntegrationSpaceCast J)
                               _ _ _ (LElemProductIntegrableAEspec l x d0));
      apply (@IntegralExtensional (IntegrationSpaceCast J)).
      intros. destruct xdf, xdg. unfold ProdLFunc.
      apply CRplus_morph.
      apply CRmult_morph. apply CRmult_morph.
      reflexivity. apply DomainProp. apply DomainProp. simpl. apply DomainProp.
    + apply IntegrablePlus. 2: exact IHl. clear IHl.
      apply ProdIntegrableFuncIntegrable.
Qed.

Lemma IElemProductFubini
  : forall { I J : IntegrationSpace }
      (f : PartialFunction (prod (X (ElemFunc I)) (X (ElemFunc J))))
      (l : list ProdIntegrable)
      (res : PartialRestriction (ProdLFunc l) f),
    IElemProduct f (existT _ l res)
    == Integral (LElemProductIntegralFstIntegrable l).
Proof.
  intros. simpl. clear res f. induction l.
  - simpl. rewrite <- (@IntegralZeroIsZero I). apply IntegralExtensional.
    simpl. intros.
    rewrite (@IntegralExtensional
               (IntegrationSpaceCast J)
               _ _ (LElemProductIntegrableAEspec nil x xdg) IntegrableZero).
    symmetry. apply (@IntegralZeroIsZero (IntegrationSpaceCast J)).
    reflexivity.
  - simpl. rewrite IHl. clear IHl.
    setoid_replace (prodint_factor a * MeasureSet (prodint_fint a)
                    * CRcast (MeasureSet (prodint_gint a)))
      with (Integral (ProdIntegrableFuncIntegrable a)).
    + rewrite <- (@IntegralPlus I). apply IntegralExtensional.
      intros; simpl in xdf, xdg.
      destruct xdf as [s d].
      unfold Xplus, XbinOp, XbinOpXY, IntegralFst, partialApply.
      unfold ProdIntegrableFuncIntegrableAE.
      rewrite IntegralRestrict.
      rewrite <- (@IntegralPlus (IntegrationSpaceCast J)
                              _ _ _ (LElemProductIntegrableAEspec l x d));
      apply (@IntegralExtensional (IntegrationSpaceCast J)). intros.
      destruct xdf, xdg0, d2. simpl.
      apply CRplus_morph. 2: apply DomainProp.
      destruct s. destruct d2. 2: contradiction.
      destruct d0. destruct d4. reflexivity. contradiction.
      destruct d4. contradiction. reflexivity.
      destruct d2. contradiction.
      rewrite CRmult_0_r, CRmult_0_l, CRmult_0_l. reflexivity.
    + unfold ProdIntegrableFuncIntegrable; rewrite IntegralRestrict.
      rewrite IntegralScale. rewrite (CRmult_comm (Integral (prodint_fint a))).
      do 2 rewrite CRmult_assoc. apply CRmult_morph. reflexivity.
      rewrite CRmult_comm. reflexivity.
Qed.

Lemma IElemProductAdditive
  : forall { I J : IntegrationSpace }
      (f g : PartialFunction (prod (X (ElemFunc I)) (X (ElemFunc J))))
      (fL : L (ProductFunctionRieszSpace I J) f)
      (gL : L (ProductFunctionRieszSpace I J) g),
    IElemProduct (Xplus f g) (LplusStable (ProductFunctionRieszSpace I J) f g fL gL)
    == IElemProduct f fL + IElemProduct g gL.
Proof.
  intros. simpl; unfold IElemProduct; destruct fL as [fl fL]; destruct gL as [gl gL].
  clear gL g fL f. induction fl.
  - simpl (fold_right (CRplus (RealT (ElemFunc I))) 0
    (map
       (fun pi : ProdIntegrable =>
          prodint_factor pi * MeasureSet (prodint_fint pi) * MeasureSet (prodint_gint pi)) nil)).
    rewrite CRplus_0_l. reflexivity.
  - simpl. rewrite IHfl. rewrite CRplus_assoc. reflexivity.
Qed.

Lemma IElemProductHomogeneous
  : forall { I J : IntegrationSpace }
      (a : CRcarrier (RealT (ElemFunc I)))
      (f : PartialFunction (prod (X (ElemFunc I)) (X (ElemFunc J))))
      (fL : L (ProductFunctionRieszSpace I J) f),
    IElemProduct (Xscale a f) (LscaleStable (ProductFunctionRieszSpace I J) a f fL)
    == a * (IElemProduct f fL).
Proof.
  intros. simpl; unfold IElemProduct; destruct fL as [l fL].
  clear fL f. induction l.
  - simpl. rewrite CRmult_0_r. reflexivity.
  - simpl. rewrite IHl. do 2 rewrite CRmult_assoc.
    rewrite <- CRmult_plus_distr_l. apply CRmult_morph. reflexivity.
    rewrite CRmult_assoc. reflexivity.
Qed.

Lemma IElemProductOneL
  : forall { I J : IntegrationSpace }
      (A : X (ElemFunc I) -> Prop) (B : X (ElemFunc J) -> Prop)
      (Aint : IntegrableSet A) (Bint : IntegrableSet B)
      (alpha : CRcarrier (RealT (ElemFunc I))),
    L (ProductFunctionRieszSpace I J)
      (ProdIntegrableFunc
         (Build_ProdIntegrable I J A B alpha Aint Bint)).
Proof.
  intros. exists ((Build_ProdIntegrable I J A B alpha Aint Bint) :: nil).
  split.
  - intros [x y] H; apply H.
  - intros. simpl in xD, xG. unfold ProdLFunc.
    rewrite <- (CRplus_0_r ( partialApply (ProdIntegrableFunc
       {|
       prodint_f := A;
       prodint_g := B;
       prodint_factor := alpha;
       prodint_fint := Aint;
       prodint_gint := Bint |}) x xG)).
    destruct xD. apply CRplus_morph.
    apply DomainProp. reflexivity.
Defined.

Lemma IntegralFstNonNeg
  : forall { I J : IntegrationSpace }
      (f : PartialFunction (prod (X (ElemFunc I)) (X (ElemFunc J))))
      (fInt : IntegrableFunctionAE f),
    nonNegFunc f
    -> nonNegFunc (IntegralFst f fInt).
Proof.
  intros. intros x xdf.
  destruct fInt, p; simpl; simpl in xdf.
  apply (@IntegralNonNeg (IntegrationSpaceCast J)). intros y ydf. apply H.
Qed.

Lemma applyIntegralFst
  : forall { I J : IntegrationSpace }
      (l : list (@ProdIntegrable I J))
      (x : X (ElemFunc I))
      (lint : @IntegrableFunction (IntegrationSpaceCast J) (Xproj1 (ProdLFunc l) x))
      (xD : Domain (IntegralFst (ProdLFunc l) (LElemProductIntegrableAE l)) x),
    partialApply _ x xD == Integral lint.
Proof.
  intros. apply (@IntegralExtensional (IntegrationSpaceCast J)).
  intros. apply DomainProp.
Qed.

Lemma IElemProductExtensional
  : forall { I J : IntegrationSpace }
      (f : PartialFunction (X (ProductFunctionRieszSpace I J)))
      (fl : list (@ProdIntegrable I J))
      (fres : PartialRestriction (ProdLFunc fl) f)
      (g : PartialFunction (X (ProductFunctionRieszSpace I J)))
      (gL : L (ProductFunctionRieszSpace I J) g) ,
    (forall x (xD : Domain (ProdLFunc fl) x) (yD : Domain g x),
        partialApply _ x xD == partialApply g x yD)
    -> IElemProduct f (existT _ fl fres) == IElemProduct g gL.
Proof.
  intros I J f fl fres g gL res. destruct gL.
  do 2 rewrite IElemProductFubini. apply IntegralExtensional.
  intros. simpl. apply (@IntegralExtensional (IntegrationSpaceCast J)).
  intros. simpl. destruct p, fres.
  rewrite (c _ xdg0 (d _ xdg0)). apply res.
Qed.

Lemma applyProdLFuncBound
  : forall { I J : IntegrationSpace }
      (l : list (@ProdIntegrable I J))
      x (xD : Domain (ProdLFunc l) x),
    partialApply _ x xD
    <= fold_right (CRplus (RealT (ElemFunc I))) 0 (map (fun a => CRabs _ (prodint_factor a)) l).
Proof.
  induction l.
  - intros. apply CRle_refl.
  - intros. simpl. destruct xD. apply CRplus_le_compat.
    destruct d. simpl. destruct d. destruct d1.
    do 2 rewrite CRmult_1_r. apply CRle_abs.
    rewrite CRmult_0_r. apply CRabs_pos.
    rewrite CRmult_0_r, CRmult_0_l. apply CRabs_pos.
    apply IHl.
Qed.

Lemma seq_cv_0_bound
  : forall {R : ConstructiveReals} (u v : nat -> CRcarrier R),
    (forall n:nat, 0 <= u n)
    -> (forall n:nat, u n <= v n)
    -> CR_cv R v 0
    -> CR_cv R u 0.
Proof.
  intros. intro p. specialize (H1 p) as [n H1]. exists n.
  intros. unfold CRminus. rewrite CRopp_0, CRplus_0_r.
  rewrite CRabs_right. specialize (H1 i H2).
  unfold CRminus in H1.
  rewrite CRopp_0, CRplus_0_r, CRabs_right in H1.
  exact (CRle_trans _ (v i) _ (H0 i) H1).
  exact (CRle_trans _ (u i) _ (H i) (H0 i)).
  exact (H i).
Qed.

Lemma seq_cv_0_mult
  : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (a : CRcarrier R),
    CR_cv R u 0
    -> CR_cv R (fun n => u n * a) 0.
Proof.
  intros R u a H p.
  destruct (CRup_nat (CRabs _ a)) as [n nup].
  destruct (H (p * Pos.of_nat n)%positive) as [k kmaj].
  exists k. intros.
  unfold CRminus. rewrite CRopp_0, CRplus_0_r.
  specialize (kmaj i H0).
  unfold CRminus in kmaj. rewrite CRopp_0, CRplus_0_r in kmaj.
  rewrite CRabs_mult.
  apply (CRmult_le_compat_r (CR_of_Q R (Z.of_nat n # 1))) in kmaj.
  rewrite <- CR_of_Q_mult in kmaj.
  setoid_replace ((1 # p * Pos.of_nat n) * (Z.of_nat n # 1))%Q with (1#p)%Q in kmaj.
  apply (CRle_trans _ (CRabs _ (u i) * CR_of_Q R (Z.of_nat n # 1))).
  apply CRmult_le_compat_l. apply CRabs_pos.
  apply CRlt_asym, nup. exact kmaj.
  unfold Qmult, Qnum, Qden. rewrite Z.mul_1_l, Pos.mul_1_r.
  unfold Qeq, Qnum, Qden. rewrite Z.mul_1_l.
  rewrite Pos2Z.inj_mul, Z.mul_comm.
  unfold Z.of_nat. simpl. destruct n. exfalso.
  simpl in nup. rewrite CR_of_Q_zero in nup. exact (CRabs_pos a nup).
  rewrite Pos.of_nat_succ. reflexivity. rewrite <- CR_of_Q_zero.
  apply CR_of_Q_le. unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
  apply Zle_0_nat.
Qed.

Lemma ProductMinLimitDecr
  : forall { I J : IntegrationSpace }
      (g : PartialFunction (X (ProductFunctionRieszSpace I J)))
      (gL : L (ProductFunctionRieszSpace I J) g),
    nonNegFunc g
    -> CR_cv _
        (fun n : nat =>
           IElemProduct (XminConst g (CR_of_Q _ (1 # Pos.of_nat (S n))))
                        (LminConstStable (CR_of_Q _ (1 # Pos.of_nat (S n))) g (invSuccRealPositive n)
                                         gL)) 0.
Proof.
  intros. destruct gL as [l res].
  assert (forall n:nat,
       IElemProduct (ProdLFunc (map (ProdIntegrableMapCoef (fun x => CRmin x (CR_of_Q _ (1 # Pos.of_nat (S n))))) (ProdIntegrableSimplify l)))
                    (existT _ (map (ProdIntegrableMapCoef (fun x => CRmin x (CR_of_Q _ (1 # Pos.of_nat (S n))))) (ProdIntegrableSimplify l)) (PartialRestriction_refl _ _))
       == IElemProduct (XminConst g (CR_of_Q _ (1 # Pos.of_nat (S n))))
       (LminConstStable (CR_of_Q _ (1 # Pos.of_nat (S n))) g (invSuccRealPositive n)
                        (existT (fun l0 : list ProdIntegrable => PartialRestriction (ProdLFunc l0) g) l res))).
  { intro n. apply IElemProductExtensional.
    intros.
    destruct (ProductMinConstStable
                l (CR_of_Q _ (1 # Pos.of_nat (S n))) (invSuccRealPositive n)).
    rewrite (c x xD (d x xD)). unfold XminConst, Xop, partialApply.
    destruct res.
    rewrite (c0 x (d x xD) yD). reflexivity. }
  apply (CR_cv_eq
           _ (fun n => IElemProduct (ProdLFunc (map (ProdIntegrableMapCoef (fun x => CRmin x (CR_of_Q _ (1 # Pos.of_nat (S n))))) (ProdIntegrableSimplify l)))
                                 (existT _ (map (ProdIntegrableMapCoef (fun x => CRmin x (CR_of_Q _ (1 # Pos.of_nat (S n))))) (ProdIntegrableSimplify l)) (PartialRestriction_refl _ _)))).
  exact H0.

  apply (seq_cv_0_bound
           _ (fun n => CR_of_Q _ (1 # Pos.of_nat (S n))
                    * fold_right (CRplus (RealT (ElemFunc I))) 0
                                 (map
                                    (fun pi : ProdIntegrable =>
                                       MeasureSet (prodint_fint pi) * CRcast (MeasureSet (prodint_gint pi)))
                                    (ProdIntegrableSimplify l)))).
  - intro n. rewrite H0.
    destruct (LminConstStable (CR_of_Q _ (1 # Pos.of_nat (S n))) g (invSuccRealPositive n)
                              (existT (fun l0 : list ProdIntegrable => PartialRestriction (ProdLFunc l0) g) l res)).
    rewrite IElemProductFubini. apply IntegralNonNeg.
    intros x0 xdf. simpl. apply (@IntegralNonNeg (IntegrationSpaceCast J)).
    intros x1 xdf0. simpl. destruct p.
    rewrite (c _ xdf0 (d _ xdf0)).
    apply CRmin_glb. apply H. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate.
  - intro n. generalize (ProdIntegrableSimplify l).
    induction l0. simpl (fold_right (CRplus _) 0
                                    (map (fun pi : ProdIntegrable => MeasureSet (prodint_fint pi) * MeasureSet (prodint_gint pi)) nil)).
    rewrite CRmult_0_r. apply CRle_refl.
    simpl (fold_right (CRplus _) 0
                      (map (fun pi : ProdIntegrable => MeasureSet (prodint_fint pi)
                                                    * CRcast (MeasureSet (prodint_gint pi)))
                           (a :: l0))).
    rewrite CRmult_plus_distr_l. apply CRplus_le_compat. 2: exact IHl0.
    destruct a;
      unfold prodint_gint, prodint_fint, ProdIntegrableMapCoef,
      prodint_factor, prodint_gint, prodint_fint.
    rewrite CRmult_assoc.
    apply CRmult_le_compat_r.
    rewrite <- (CRmult_0_l (CRcast (MeasureSet prodint_gint0))).
    apply CRmult_le_compat_r.
    unfold CRcast.
    rewrite <- (CRmorph_zero (@SlowConstructiveRealsMorphism (RealT (ElemFunc J)) (RealT (ElemFunc I)))).
    apply CRmorph_le. apply MeasureNonNeg. apply MeasureNonNeg.
    apply CRmin_r.
  - apply seq_cv_0_mult.
    intro p. exists (Pos.to_nat p). intros.
    unfold CRminus. rewrite CRopp_0, CRplus_0_r, CRabs_right.
    apply CR_of_Q_le. unfold Qle, Qnum, Qden.
    do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos, Pos2Nat.inj_le.
    rewrite Nat2Pos.id. 2: discriminate. apply (le_trans _ _ _ H1).
    apply le_S, le_refl. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate.
Qed.

Lemma ProductMinLimits
  : forall { I J : IntegrationSpace }
      (f : PartialFunction (X (ProductFunctionRieszSpace I J)))
      (fL : L (ProductFunctionRieszSpace I J) f),
    CR_cv _
      (fun n : nat => IElemProduct (XminConst f (ConstructiveSum.INR n)) (LminIntStable n f fL))
      (IElemProduct f fL) *
    CR_cv _
      (fun n : nat =>
         IElemProduct (XminConst (Xabs f) (CR_of_Q _ (1 # Pos.of_nat (S n))))
                      (LminConstStable (CR_of_Q _ (1 # Pos.of_nat (S n))) (Xabs f) (invSuccRealPositive n)
                                       (LabsStable (ProductFunctionRieszSpace I J) f fL))) 0.
Proof.
  intros. split.
  - (* A sum of ProdIntegrableFunc is majorated by the sum
       of the product factors. *)
    destruct fL as [l fL].
    destruct (CRup_nat (fold_right (CRplus _) 0 (map (fun a => CRabs _ (prodint_factor a)) l)))
      as [n nup].
    exists n. intros.
    setoid_replace (IElemProduct (XminConst f (ConstructiveSum.INR i))
       (LminIntStable i f
          (existT (fun l0 : list ProdIntegrable => PartialRestriction (ProdLFunc l0) f) l fL)) -
                    IElemProduct f (existT (fun l0 : list ProdIntegrable => PartialRestriction (ProdLFunc l0) f) l fL))
      with (CRzero (RealT (ElemFunc I))).
    rewrite CRabs_right. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_le. discriminate. apply CRle_refl.
    rewrite <- (CRplus_opp_r (IElemProduct f (existT (fun l0 : list ProdIntegrable => PartialRestriction (ProdLFunc l0) f) l fL))).
    apply CRplus_morph. 2: reflexivity.
    symmetry.
    apply IElemProductExtensional.
    intros. unfold XminConst, Xop, partialApply. rewrite CRmin_left.
    destruct fL. rewrite (c x xD (d x xD)). apply DomainProp.
    simpl in yD.
    destruct fL. rewrite <- (c x xD).
    apply (CRle_trans _ _ _ (applyProdLFuncBound l x xD)).
    apply (CRle_trans _ (CR_of_Q _ (Z.of_nat n # 1))).
    apply CRlt_asym, nup. apply CR_of_Q_le.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r.
    apply Nat2Z.inj_le, H.
  - (* The sequences finishes integrating a constant function. *)
    apply ProductMinLimitDecr.
    intros x xdf. apply CRabs_pos.
Qed.

Lemma ProductIContinuous { I J : IntegrationSpace }
  : @ElemIntegralContinuous
      (ProductFunctionRieszSpace I J) IElemProduct.
Proof.
  intros f fn fL fnL fnNonNeg cv.
  destruct fL as [fl fL].
  pose (fun n => let (l,_) := fnL n in l) as ln.
  assert (forall n:nat, PartialRestriction (ProdLFunc (ln n)) (fn n)) as resn.
  { intro n. unfold ln. destruct (fnL n). exact p. }
  destruct (IntegrableContinuous
              (IntegralFst (ProdLFunc fl) (LElemProductIntegrableAE fl))
              (fun n => IntegralFst (ProdLFunc (ln n)) (LElemProductIntegrableAE (ln n)))
              (LElemProductIntegralFstIntegrable fl)
              (fun n => LElemProductIntegralFstIntegrable (ln n)))
    as [x [limx xcv]].
  intro n. apply IntegralFstNonNeg.
  intros t tdf. destruct (resn n).
  rewrite (c t tdf (d t tdf)). apply fnNonNeg.
  destruct cv, p. simpl in x. exists x. split.
  apply (series_cv_eq (fun n : nat => IElemProduct (fn n) (fnL n))).
  2: exact s. intro n. unfold ln. destruct (fnL n).
  rewrite IElemProductFubini. reflexivity.
  simpl. rewrite IElemProductFubini in c. exact c.
  assert (forall n:nat,
             Domain (XsumList (map (fun x : ProdIntegrable => @CharacFunc (RealT (ElemFunc I)) _ (prodint_f x)) (ln n)))
                    (cpx _ _ _ x)) as H2.
  { intro n. apply (cpxFn _ _ _ x n). }
  assert (forall n:nat, @IntegrableFunction (IntegrationSpaceCast J)
                   (Xproj1 (ProdLFunc (ln n)) (cpx _ _ _ x)))
    as fnInt.
  { intro n. specialize (H2 n). unfold ln. unfold ln in H2.
    destruct (fnL n).
    apply LElemProductIntegrableAEspec. exact H2. }
  destruct (@IntegrableContinuous (IntegrationSpaceCast J)
              (Xproj1 (ProdLFunc fl) (cpx _ _ _ x))
              (fun n => Xproj1 (ProdLFunc (ln n)) (cpx _ _ _ x))
              (LElemProductIntegrableAEspec fl (cpx _ _ _ x) (cpxF _ _ _ x))
              fnInt)
    as [y ycv].
  intro n. intros y ydf.
  pose proof (Xproj1Restriction _ _ (cpx _ _ _ x) (resn n)) as [d c].
  rewrite (c y ydf (d y ydf)). apply fnNonNeg.
  exists limx. destruct xcv. split.
  apply (series_cv_eq (fun n : nat =>
                         partialApply
                           (IntegralFst (ProdLFunc (ln n)) (LElemProductIntegrableAE (ln n)))
                           (cpx _ _ _ x)
                           (cpxFn _ _ _ x n))).
  2: exact s. intro n. apply applyIntegralFst.
  destruct x. simpl in c. simpl. exact c.
  destruct fL.
  assert (forall n : nat, DomainInclusion (ProdLFunc (ln n)) (fn n)) as incn.
  { intro n. destruct (resn n). exact d0. }
  exists (Build_CommonPointFunSeq
       _ _ f fn (cpx _ _ _ x, cpx _ _ _ y)
       (d (cpx _ _ _ x, cpx _ _ _ y) (cpxF _ _ _ y))
       (fun n => incn n (cpx _ _ _ x, cpx _ _ _ y) (cpxFn _ _ _ y n)));
    unfold cpx, cpxF, cpxFn. destruct ycv as [y0 [ycv ylt]].
  exists y0. split.
  apply (series_cv_eq (fun n : nat =>
                         partialApply
                           (Xproj1 (ProdLFunc (ln n))
                                   (cpx (X (ElemFunc I)) (IntegralFst (ProdLFunc fl) (LElemProductIntegrableAE fl))
                                        (fun n0 : nat => IntegralFst (ProdLFunc (ln n0)) (LElemProductIntegrableAE (ln n0)))
                                        x))
                           (cpx _ _ _ y)
                           (cpxFn _ _ _ y n))).
  2: exact ycv. intro n. destruct (resn n). apply c0.
  simpl in ylt; rewrite c in ylt; exact ylt.
Qed.

Definition ProductIntegrationSpace
           (I J : IntegrationSpace)
  : IntegrationSpace.
Proof.
  intros.
  destruct (PositiveMeasureSubsetExists I) as [A Aint H].
  destruct (PositiveMeasureSubsetExists J) as [B Bint H0].
  apply (Build_IntegrationSpace
           (ProductFunctionRieszSpace I J)
           IElemProduct IElemProductAdditive IElemProductHomogeneous
           (ProdIntegrableFunc
              (Build_ProdIntegrable
                 I J A B (CRinv _ (MeasureSet Aint) (inr H)
                          * CRcast (CRinv _ (MeasureSet Bint) (inr H0)))
                 Aint Bint))
           (IElemProductOneL A B Aint Bint _)).
  - unfold IElemProduct, IElemProductOneL, map, fold_left, prodint_factor.
    unfold prodint_fint, prodint_gint, fold_right.
    rewrite CRplus_0_r, CRmult_assoc, (CRmult_comm (MeasureSet Aint)).
    rewrite CRmult_assoc.
    rewrite <- (CRmult_assoc (CRcast (CRinv (RealT (ElemFunc J)) (MeasureSet Bint) (inr H0)))).
    unfold CRcast. rewrite <- CRmorph_mult.
    rewrite (CRmorph_proper _ (CRinv (RealT (ElemFunc J)) (MeasureSet Bint) (inr H0) * MeasureSet Bint) 1).
    rewrite CRmorph_one, CRmult_1_l. apply CRinv_l. apply CRinv_l.
  - apply ProductIContinuous.
  - apply ProductMinLimits.
Defined.
