(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The first three levels of homotopy type theory: homotopy propositions,
    homotopy sets and homotopy one types. For more information,
    https://github.com/HoTT/HoTT
    and
    https://homotopytypetheory.org/book

    Univalence is not assumed here, and equality is Coq's usual inductive
    type eq in sort Prop. This is a little different from HoTT, where
    sort Prop does not exist and equality is directly in sort Type. *)

(* A homotopy proposition is a type that has at most one element.
   Its unique inhabitant, when it exists, is to be interpreted as the
   proof of the homotopy proposition.
   Homotopy propositions are therefore an alternative to the sort Prop,
   to select which types represent mathematical propositions. *)
Definition IsHProp (P : Type) : Prop
  := forall p q : P, p = q.

(* A homotopy set is a type such as each equality type x = y is a
   homotopy proposition. For example, any type which equality is
   decidable in sort Prop is a homotopy set, as shown in file
   Stdlib.Logic.Eqdep_dec.v. *)
Definition IsHSet (X : Type) : Prop
  := forall (x y : X) (p q : x = y), p = q.

Definition IsHOneType (X : Type) : Prop
  := forall (x y : X) (p q : x = y) (r s : p = q), r = s.

(* Homotopy propositions are stable by conjunction, but not by disjunction,
   which can have a proof by the left and another proof by the right. *)
Lemma and_hprop : forall P Q : Prop,
    IsHProp P -> IsHProp Q -> IsHProp (P /\ Q).
Proof.
  intros. intros p q. destruct p,q.
  replace p0 with p.
  - replace q0 with q.
    + reflexivity.
    + apply H0.
  - apply H.
Qed.

(* Homotopy propositions are included in homotopy sets.
   They are the first 2 levels of a cumulative hierarchy of types
   indexed by the natural numbers. In homotopy type theory,
   homotopy propositions are call (-1)-types and homotopy
   sets 0-types. *)
Lemma hset_hprop : forall X : Type,
    IsHProp X -> IsHSet X.
Proof.
  intros X H.
  assert (forall (x y z:X) (p : y = z), eq_trans (H x y) p = H x z).
  { intros. unfold eq_trans, eq_ind. destruct p. reflexivity. }
  assert (forall (x y z:X) (p : y = z),
             p = eq_trans (eq_sym (H x y)) (H x z)).
  { intros. rewrite <- (H0 x y z p). unfold eq_trans, eq_sym, eq_ind.
    destruct p, (H x y). reflexivity. }
  intros x y p q.
  rewrite (H1 x x y p), (H1 x x y q). reflexivity.
Qed.

Lemma eq_trans_cancel : forall {X : Type} {x y z : X} (p : x = y) (q r : y = z),
  (eq_trans p q = eq_trans p r) -> q = r.
Proof.
  intros. destruct p. simpl in H. destruct r.
  simpl in H. rewrite eq_trans_refl_l in H. exact H.
Qed.

Lemma hset_hOneType : forall X : Type,
    IsHSet X -> IsHOneType X.
Proof.
  intros X f x y p q.
  pose (fun a => f x y p a) as g.
  assert (forall a (r : q = a), eq_trans (g q) r = g a).
  { intros. destruct a. subst q. reflexivity. }
  intros r s. pose proof (H p (eq_sym r)).
  pose proof (H p (eq_sym s)).
  rewrite <- H1 in H0. apply eq_trans_cancel in H0.
  rewrite <- eq_sym_involutive. rewrite <- (eq_sym_involutive r).
  rewrite H0. reflexivity.
Qed.

Definition false_hprop : IsHProp False :=
  fun p => match p with end.

Definition true_hprop : IsHProp True :=
  fun p q => match p, q with I, I => eq_refl end.
