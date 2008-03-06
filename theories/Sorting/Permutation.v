(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Coq.Relations.Relations.
Require Import List.
Require Import Multiset.
Require Import Arith.

(** This file define a notion of permutation for lists, based on multisets: 
    there exists a permutation between two lists iff every elements have 
    the same multiplicities in the two lists. 

    Unlike [List.Permutation], the present notion of permutation requires
    a decidable equality. At the same time, this definition can be used 
    with a non-standard equality, whereas [List.Permutation] cannot.
      
    The present file contains basic results, obtained without any particular
    assumption on the decidable equality used.
	
    File [PermutSetoid] contains additional results about permutations 
    with respect to an setoid equality (i.e. an equivalence relation). 

    Finally, file [PermutEq] concerns Coq equality : this file is similar 
    to the previous one, but proves in addition that [List.Permutation]
    and [permutation] are equivalent in this context.
x*)

Set Implicit Arguments.

Section defs.

  (** * From lists to multisets *)

  Variable A : Type.
  Variable eqA : relation A.
  Hypothesis eqA_dec : forall x y:A, {eqA x y} + {~ eqA x y}.

  Let emptyBag := EmptyBag A.
  Let singletonBag := SingletonBag _ eqA_dec.

  (** contents of a list *)

  Fixpoint list_contents (l:list A) : multiset A :=
    match l with
      | nil => emptyBag
      | a :: l => munion (singletonBag a) (list_contents l)
    end.

  Lemma list_contents_app :
    forall l m:list A,
      meq (list_contents (l ++ m)) (munion (list_contents l) (list_contents m)).
  Proof.
    simple induction l; simpl in |- *; auto with datatypes.
    intros.
    apply meq_trans with
      (munion (singletonBag a) (munion (list_contents l0) (list_contents m)));
      auto with datatypes.
  Qed.

  
  (** * [permutation]: definition and basic properties *)
  
  Definition permutation (l m:list A) :=
    meq (list_contents l) (list_contents m).

  Lemma permut_refl : forall l:list A, permutation l l.
  Proof.
    unfold permutation in |- *; auto with datatypes.
  Qed.
  
  Lemma permut_sym :
    forall l1 l2 : list A, permutation l1 l2 -> permutation l2 l1.
  Proof.
    unfold permutation, meq; intros; apply sym_eq; trivial.
  Qed.
  
  Lemma permut_tran :
    forall l m n:list A, permutation l m -> permutation m n -> permutation l n.
  Proof.
    unfold permutation in |- *; intros.
    apply meq_trans with (list_contents m); auto with datatypes.
  Qed.
  
  Lemma permut_cons :
    forall l m:list A,
      permutation l m -> forall a:A, permutation (a :: l) (a :: m).
  Proof.
    unfold permutation in |- *; simpl in |- *; auto with datatypes.
  Qed.
  
  Lemma permut_app :
    forall l l' m m':list A,
      permutation l l' -> permutation m m' -> permutation (l ++ m) (l' ++ m').
  Proof.
    unfold permutation in |- *; intros.
    apply meq_trans with (munion (list_contents l) (list_contents m)); 
      auto using permut_cons, list_contents_app with datatypes.
    apply meq_trans with (munion (list_contents l') (list_contents m')); 
      auto using permut_cons, list_contents_app with datatypes.
    apply meq_trans with (munion (list_contents l') (list_contents m));
      auto using permut_cons, list_contents_app with datatypes.
  Qed.

  Lemma permut_add_inside :
    forall a l1 l2 l3 l4, 
      permutation (l1 ++ l2) (l3 ++ l4) ->
      permutation (l1 ++ a :: l2) (l3 ++ a :: l4).
  Proof.
    unfold permutation, meq in *; intros.
    generalize (H a0); clear H.
    do 4 rewrite list_contents_app.
    simpl.
    destruct (eqA_dec a a0); simpl; auto with arith.
    do 2 rewrite <- plus_n_Sm; f_equal; auto.
  Qed.
  
  Lemma permut_add_cons_inside :
    forall a l l1 l2, 
      permutation l (l1 ++ l2) ->
      permutation (a :: l) (l1 ++ a :: l2).
  Proof.
    intros;
      replace (a :: l) with (nil ++ a :: l); trivial;
	apply permut_add_inside; trivial.
  Qed.

  Lemma permut_middle :
    forall (l m:list A) (a:A), permutation (a :: l ++ m) (l ++ a :: m).
  Proof.
    intros; apply permut_add_cons_inside; auto using permut_sym, permut_refl.
  Qed.
  
  Lemma permut_sym_app :
    forall l1 l2, permutation (l1 ++ l2) (l2 ++ l1).
  Proof.
    intros l1 l2;
      unfold permutation, meq; 
	intro a; do 2 rewrite list_contents_app; simpl; 
	  auto with arith.
  Qed.

  Lemma permut_rev : 
    forall l, permutation l (rev l).
  Proof.
    induction l.
    simpl; trivial using permut_refl.
    simpl.
    apply permut_add_cons_inside.
    rewrite <- app_nil_end. trivial.
  Qed.

  (** * Some inversion results. *)
  Lemma permut_conv_inv :
    forall e l1 l2, permutation (e :: l1) (e :: l2) -> permutation l1 l2.
  Proof.
    intros e l1 l2; unfold permutation, meq; simpl; intros H a;
      generalize (H a); apply plus_reg_l.
  Qed.

  Lemma permut_app_inv1 : 
    forall l l1 l2, permutation (l1 ++ l) (l2 ++ l) -> permutation l1 l2.
  Proof.
    intros l l1 l2; unfold permutation, meq; simpl;
      intros H a; generalize (H a); clear H.
    do 2 rewrite list_contents_app.
    simpl.
    intros; apply plus_reg_l with (multiplicity (list_contents l) a).
    rewrite plus_comm; rewrite H; rewrite plus_comm.
    trivial.
  Qed.

  Lemma permut_app_inv2 : 
    forall l l1 l2, permutation (l ++ l1) (l ++ l2) -> permutation l1 l2.
  Proof.
    intros l l1 l2; unfold permutation, meq; simpl;
      intros H a; generalize (H a); clear H.
    do 2 rewrite list_contents_app.
    simpl.
    intros; apply plus_reg_l with (multiplicity (list_contents l) a).
    trivial.
  Qed.

  Lemma permut_remove_hd :
    forall l l1 l2 a,   
      permutation (a :: l) (l1 ++ a :: l2) -> permutation l (l1 ++ l2).
  Proof.
    intros l l1 l2 a; unfold permutation, meq; simpl; intros H a0; generalize (H a0); clear H.
    do 2 rewrite list_contents_app; simpl; intro H.
    apply plus_reg_l with (if eqA_dec a a0 then 1 else 0).
    rewrite H; clear H.
    symmetry; rewrite plus_comm.
    repeat rewrite <- plus_assoc; f_equal.
    apply plus_comm.
  Qed.

End defs.

(** For compatibilty *) 
Notation permut_right := permut_cons.
Unset Implicit Arguments.
