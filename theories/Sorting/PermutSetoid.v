(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Omega Coq.Relations.Relations Multiset Permutation SetoidList.

Set Implicit Arguments.

(** This file contains additional results about permutations 
     with respect to an setoid equality (i.e. an equivalence relation). 
*)

Section Perm.

Variable A : Type.
Variable eqA : relation A.
Hypothesis eqA_dec : forall x y:A, {eqA x y} + {~ eqA x y}.

Notation permutation := (permutation _ eqA_dec).
Notation list_contents := (list_contents _ eqA_dec).

(** The following lemmas need some knowledge on [eqA] *)

Variable eqA_refl : forall x, eqA x x.
Variable eqA_sym : forall x y, eqA x y -> eqA y x.
Variable eqA_trans : forall x y z, eqA x y -> eqA y z -> eqA x z.

(** we can use [multiplicity] to define [InA] and [NoDupA]. *)

Lemma multiplicity_InA : 
  forall l a, InA eqA a l <-> 0 < multiplicity (list_contents l) a.
Proof.
  induction l.
  simpl.
  split; inversion 1.
  simpl.
  split; intros.
  inversion_clear H.
  destruct (eqA_dec a a0) as [_|H1]; auto with arith.
  destruct H1; auto.
  destruct (eqA_dec a a0); auto with arith.
  simpl; rewrite <- IHl; auto.
  destruct (eqA_dec a a0) as [H0|H0]; auto.
  simpl in H.
  constructor 2; rewrite IHl; auto.
Qed.

Lemma multiplicity_InA_O :
  forall l a, ~ InA eqA a l -> multiplicity (list_contents l) a = 0.
Proof.
  intros l a; rewrite multiplicity_InA; 
    destruct (multiplicity (list_contents l) a); auto with arith.
  destruct 1; auto with arith.
Qed.

Lemma multiplicity_InA_S :
  forall l a, InA eqA a l -> multiplicity (list_contents l) a >= 1.
Proof.
  intros l a; rewrite multiplicity_InA; auto with arith.
Qed.

Lemma multiplicity_NoDupA : forall l, 
  NoDupA eqA l <-> (forall a, multiplicity (list_contents l) a <= 1).
Proof.
  induction l.
  simpl.
  split; auto with arith.
  split; simpl.
  inversion_clear 1.
  rewrite IHl in H1.
  intros; destruct (eqA_dec a a0) as [H2|H2]; simpl; auto.
  rewrite multiplicity_InA_O; auto.
  contradict H0.
  apply InA_eqA with a0; auto.
  intros; constructor.
  rewrite multiplicity_InA.
  generalize (H a).
  destruct (eqA_dec a a) as [H0|H0].
  destruct (multiplicity (list_contents l) a); auto with arith.
  simpl; inversion 1. 
  inversion H3.
  destruct H0; auto.
  rewrite IHl; intros.
  generalize (H a0); auto with arith.
  destruct (eqA_dec a a0); simpl; auto with arith.
Qed.


(** Permutation is compatible with InA. *)
Lemma permut_InA_InA :
  forall l1 l2 e, permutation l1 l2 -> InA eqA e l1 -> InA eqA e l2.
Proof.
  intros l1 l2 e.
  do 2 rewrite multiplicity_InA.
  unfold Permutation.permutation, meq.
  intros H;rewrite H; auto.
Qed.

Lemma permut_cons_InA :
  forall l1 l2 e, permutation (e :: l1) l2 -> InA eqA e l2.
Proof.
  intros; apply (permut_InA_InA (e:=e) H); auto.
Qed.

(** Permutation of an empty list. *)
Lemma permut_nil :
  forall l, permutation l nil -> l = nil.
Proof.
  intro l; destruct l as [ | e l ]; trivial.
  assert (InA eqA e (e::l)) by auto.
  intro Abs; generalize (permut_InA_InA Abs H).
  inversion 1.
Qed.

(** Permutation for short lists. *)

Lemma permut_length_1:
  forall a b, permutation (a :: nil) (b :: nil)  -> eqA a b.
Proof.
  intros a b; unfold Permutation.permutation, meq; intro P;
  generalize (P b); clear P; simpl.
  destruct (eqA_dec b b) as [H|H]; [ | destruct H; auto].
  destruct (eqA_dec a b); simpl; auto; intros; discriminate.
Qed.

Lemma permut_length_2 :
  forall a1 b1 a2 b2, permutation (a1 :: b1 :: nil) (a2 :: b2 :: nil) ->
    (eqA a1 a2) /\ (eqA b1 b2) \/ (eqA a1 b2) /\ (eqA a2 b1).
Proof.
  intros a1 b1 a2 b2 P.
  assert (H:=permut_cons_InA P).
  inversion_clear H.
  left; split; auto.
  apply permut_length_1.
  red; red; intros.
  generalize (P a); clear P; simpl.
  destruct (eqA_dec a1 a) as [H2|H2]; 
    destruct (eqA_dec a2 a) as [H3|H3]; auto.
  destruct H3; apply eqA_trans with a1; auto.
  destruct H2; apply eqA_trans with a2; auto.
  right.
  inversion_clear H0; [|inversion H].
  split; auto.
  apply permut_length_1.
  red; red; intros.
  generalize (P a); clear P; simpl.
  destruct (eqA_dec a1 a) as [H2|H2]; 
    destruct (eqA_dec b2 a) as [H3|H3]; auto.
  simpl; rewrite <- plus_n_Sm; inversion 1; auto.
  destruct H3; apply eqA_trans with a1; auto.
  destruct H2; apply eqA_trans with b2; auto.
Qed.

(** Permutation is compatible with length. *)
Lemma permut_length :
  forall l1 l2, permutation l1 l2 -> length l1 = length l2.
Proof.
  induction l1; intros l2 H.
  rewrite (permut_nil (permut_sym H)); auto.
  assert (H0:=permut_cons_InA H).
  destruct (InA_split H0) as (h2,(b,(t2,(H1,H2)))).
  subst l2.
  rewrite app_length.
  simpl; rewrite <- plus_n_Sm; f_equal.
  rewrite <- app_length.
  apply IHl1.
  apply permut_remove_hd with b.
  apply permut_tran with (a::l1); auto.
  revert H1; unfold Permutation.permutation, meq; simpl.
  intros; f_equal; auto.
  destruct (eqA_dec b a0) as [H2|H2]; 
    destruct (eqA_dec a a0) as [H3|H3]; auto.
  destruct H3; apply eqA_trans with b; auto.
  destruct H2; apply eqA_trans with a; auto.
Qed.

Lemma NoDupA_equivlistA_permut : 
  forall l l', NoDupA eqA l -> NoDupA eqA l' -> 
    equivlistA eqA l l' -> permutation l l'.
Proof.
  intros.
  red; unfold meq; intros.
  rewrite multiplicity_NoDupA in H, H0. 
  generalize (H a) (H0 a) (H1 a); clear H H0 H1.
  do 2 rewrite multiplicity_InA.
  destruct 3; omega.
Qed.


Variable B : Type.
Variable eqB : B->B->Prop.
Variable eqB_dec : forall x y:B, { eqB x y }+{ ~eqB x y }. 
Variable eqB_trans : forall x y z, eqB x y -> eqB y z -> eqB x z.

(** Permutation is compatible with map. *)

Lemma permut_map :
  forall f, 
    (forall x y, eqA x y -> eqB (f x) (f y)) ->
    forall l1 l2, permutation l1 l2 -> 
      Permutation.permutation _ eqB_dec (map f l1) (map f l2).
Proof.
  intros f; induction l1.
  intros l2 P; rewrite (permut_nil (permut_sym P)); apply permut_refl.
  intros l2 P.
  simpl.
  assert (H0:=permut_cons_InA P).
  destruct (InA_split H0) as (h2,(b,(t2,(H1,H2)))).
  subst l2.
  rewrite map_app.
  simpl.
  apply permut_tran with (f b :: map f l1).
  revert H1; unfold Permutation.permutation, meq; simpl.
  intros; f_equal; auto.
  destruct (eqB_dec (f b) a0) as [H2|H2]; 
    destruct (eqB_dec (f a) a0) as [H3|H3]; auto.
  destruct H3; apply eqB_trans with (f b); auto.
  destruct H2; apply eqB_trans with (f a); auto.
  apply permut_add_cons_inside.
  rewrite <- map_app.
  apply IHl1; auto.
  apply permut_remove_hd with b.
  apply permut_tran with (a::l1); auto.
  revert H1; unfold Permutation.permutation, meq; simpl.
  intros; f_equal; auto.
  destruct (eqA_dec b a0) as [H2|H2]; 
    destruct (eqA_dec a a0) as [H3|H3]; auto.
  destruct H3; apply eqA_trans with b; auto.
  destruct H2; apply eqA_trans with a; auto.
Qed.

End Perm.
