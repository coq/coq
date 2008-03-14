(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite sets library.  
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre 
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

Require Import Ensembles Finite_sets.
Require Import FSetInterface FSetProperties OrderedTypeEx.

(** * Going from [FSets] with usual equality 
    to the old [Ensembles] and [Finite_sets] theory. *)

Module S_to_Finite_set (U:UsualOrderedType)(M:S with Module E := U).
 Module MP:= Properties(M).
 Import M MP FM Ensembles Finite_sets.

 Definition mkEns : M.t -> Ensemble M.elt := 
   fun s x => M.In x s.

 Notation " !! " := mkEns.

 Lemma In_In : forall s x, M.In x s <-> In _ (!!s) x.
 Proof.
 unfold In; compute; auto.
 Qed.

 Lemma Subset_Included : forall s s',  s[<=]s'  <-> Included _ (!!s) (!!s').
 Proof.
 unfold Subset, Included, In, mkEns; intuition.
 Qed.

 Notation " a === b " := (Same_set M.elt a b) (at level 70, no associativity).

 Lemma Equal_Same_set : forall s s', s[=]s' <-> !!s === !!s'.
 Proof.
 intros.
 rewrite double_inclusion.
 unfold Subset, Included, Same_set, In, mkEns; intuition.
 Qed.

 Lemma empty_Empty_Set : !!M.empty === Empty_set _.
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intro; set_iff; inversion 1.
 Qed.

 Lemma Empty_Empty_set : forall s, Empty s -> !!s === Empty_set _.
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intros.
 destruct(H x H0).
 inversion H0.
 Qed.

 Lemma singleton_Singleton : forall x, !!(M.singleton x) === Singleton _ x .
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intro; set_iff; inversion 1; try constructor; auto.
 Qed.

 Lemma union_Union : forall s s', !!(union s s') === Union _ (!!s) (!!s').
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intro; set_iff; inversion 1; [ constructor 1 | constructor 2 | | ]; auto.
 Qed.

 Lemma inter_Intersection : forall s s', !!(inter s s') === Intersection _ (!!s) (!!s').
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intro; set_iff; inversion 1; try constructor; auto.
 Qed.

 Lemma add_Add : forall x s, !!(add x s) === Add _ (!!s) x.
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intro; set_iff; inversion 1; unfold E.eq; auto with sets.
 inversion H0.
 constructor 2; constructor.
 constructor 1; auto.
 Qed.

 Lemma Add_Add : forall x s s', MP.Add x s s' -> !!s' === Add _ (!!s) x.
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intros.
 red in H; rewrite H in H0.
 destruct H0.
 inversion H0.
 constructor 2; constructor.
 constructor 1; auto.
 red in H; rewrite H; unfold E.eq in *.
 inversion H0; auto.
 inversion H1; auto.
 Qed.

 Lemma remove_Subtract : forall x s, !!(remove x s) === Subtract _ (!!s) x.
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intro; set_iff; inversion 1; unfold E.eq in *; auto with sets.
 split; auto.
 contradict H1.
 inversion H1; auto.
 Qed.

 Lemma mkEns_Finite : forall s, Finite _ (!!s).
 Proof.
 intro s; pattern s; apply set_induction; clear s; intros.
 intros; replace (!!s) with (Empty_set elt); auto with sets.
 symmetry; apply Extensionality_Ensembles. 
 apply Empty_Empty_set; auto.
 replace (!!s') with (Add _ (!!s) x).
 constructor 2; auto.
 symmetry; apply Extensionality_Ensembles. 
 apply Add_Add; auto.
 Qed.

 Lemma mkEns_cardinal : forall s, cardinal _ (!!s) (M.cardinal s).
 Proof.
 intro s; pattern s; apply set_induction; clear s; intros.
 intros; replace (!!s) with (Empty_set elt); auto with sets.
 rewrite cardinal_1; auto with sets.
 symmetry; apply Extensionality_Ensembles. 
 apply Empty_Empty_set; auto.
 replace (!!s') with (Add _ (!!s) x).
 rewrite (cardinal_2 H0 H1); auto with sets. 
 symmetry; apply Extensionality_Ensembles. 
 apply Add_Add; auto.
 Qed.

End S_to_Finite_set.
