(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite sets library : conversion to old [Finite_sets] *)

Require Import Ensembles Finite_sets.
Require Import MSetInterface MSetProperties OrdersEx.

(** * Going from [MSets] with usual Leibniz equality
    to the good old [Ensembles] and [Finite_sets] theory. *)

Module WS_to_Finite_set (U:UsualDecidableType)(M: WSetsOn U).
 Module MP:= WPropertiesOn U M.
 Import M MP FM Ensembles Finite_sets.

 Definition mkEns : M.t -> Ensemble M.elt :=
   fun s x => M.In x s.

 Notation " !! " := mkEns.

 Lemma In_In : forall s x, M.In x s <-> In _ (!!s) x.
 Proof.
 unfold In; compute; auto with extcore.
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
 split; intro; set_iff; inversion 1; auto with sets.
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
 red in H; rewrite H.
 inversion H0; auto.
 inversion H1; auto.
 Qed.

 Lemma remove_Subtract : forall x s, !!(remove x s) === Subtract _ (!!s) x.
 Proof.
 unfold Same_set, Included, mkEns, In.
 split; intro; set_iff; inversion 1; auto with sets.
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
 rewrite MP.cardinal_1; auto with sets.
 symmetry; apply Extensionality_Ensembles.
 apply Empty_Empty_set; auto.
 replace (!!s') with (Add _ (!!s) x).
 rewrite (cardinal_2 H0 H1); auto with sets.
 symmetry; apply Extensionality_Ensembles.
 apply Add_Add; auto.
 Qed.

 (** we can even build a function from Finite Ensemble to MSet
     ... at least in Prop. *)

 Lemma Ens_to_MSet : forall e : Ensemble M.elt, Finite _ e ->
   exists s:M.t, !!s === e.
 Proof.
 induction 1.
 exists M.empty.
 apply empty_Empty_Set.
 destruct IHFinite as (s,Hs).
 exists (M.add x s).
 apply Extensionality_Ensembles in Hs.
 rewrite <- Hs.
 apply add_Add.
 Qed.

End WS_to_Finite_set.


Module S_to_Finite_set (U:UsualOrderedType)(M: SetsOn U) :=
  WS_to_Finite_set U M.


