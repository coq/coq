(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Finite sets library.
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

Require Import OrderedType Orders.
Set Implicit Arguments.

(** * Some alternative (but equivalent) presentations for an Ordered Type
   inferface. *)

(** ** The original interface *)

Module Type OrderedTypeOrig := OrderedType.OrderedType.

(** ** An interface based on compare *)

Module Type OrderedTypeAlt.

 Parameter t : Type.

 Parameter compare : t -> t -> comparison.

 Infix "?=" := compare (at level 70, no associativity).

 Parameter compare_sym :
   forall x y, (y?=x) = CompOpp (x?=y).
 Parameter compare_trans :
   forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.

End OrderedTypeAlt.

(** ** From OrderedTypeOrig to OrderedType. *)

Module Update_OT (O:OrderedTypeOrig) <: OrderedType.

 Include Update_DT O.  (* Provides : t eq eq_equiv eq_dec *)

 Definition lt := O.lt.

 Instance lt_strorder : StrictOrder lt.
 Proof.
  split.
  intros x Hx. apply (O.lt_not_eq Hx); auto with *.
  exact O.lt_trans.
 Qed.

 Instance lt_compat : Proper (eq==>eq==>iff) lt.
 Proof.
  apply proper_sym_impl_iff_2; auto with *.
  intros x x' Hx y y' Hy H.
  assert (H0 : lt x' y).
   destruct (O.compare x' y) as [H'|H'|H']; auto.
   elim (O.lt_not_eq H). transitivity x'; auto with *.
   elim (O.lt_not_eq (O.lt_trans H H')); auto.
  destruct (O.compare x' y') as [H'|H'|H']; auto.
  elim (O.lt_not_eq H).
   transitivity x'; auto with *. transitivity y'; auto with *.
  elim (O.lt_not_eq (O.lt_trans H' H0)); auto with *.
 Qed.

 Definition compare x y :=
   match O.compare x y with
    | EQ _ => Eq
    | LT _ => Lt
    | GT _ => Gt
  end.

 Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
 Proof.
  intros; unfold compare; destruct O.compare; auto.
 Qed.

End Update_OT.

(** ** From OrderedType to OrderedTypeOrig. *)

Module Backport_OT (O:OrderedType) <: OrderedTypeOrig.

 Include Backport_DT O. (* Provides : t eq eq_refl eq_sym eq_trans eq_dec *)

 Definition lt := O.lt.

 Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
 Proof.
  intros x y L E; rewrite E in L. apply (StrictOrder_Irreflexive y); auto.
 Qed.

 Lemma lt_trans : Transitive lt.
 Proof. apply O.lt_strorder. Qed.

 Definition compare : forall x y, Compare lt eq x y.
 Proof.
  intros x y; destruct (CompSpec2Type (O.compare_spec x y));
   [apply EQ|apply LT|apply GT]; auto.
 Defined.

End Backport_OT.


(** ** From OrderedTypeAlt to OrderedType. *)

Module OT_from_Alt (Import O:OrderedTypeAlt) <: OrderedType.

 Definition t := t.

 Definition eq x y := (x?=y) = Eq.
 Definition lt x y := (x?=y) = Lt.

 Instance eq_equiv : Equivalence eq.
 Proof.
  split; red.
  (* refl *)
  unfold eq; intros x.
  assert (H:=compare_sym x x).
  destruct (x ?= x); simpl in *; auto; discriminate.
  (* sym *)
  unfold eq; intros x y H.
  rewrite compare_sym, H; simpl; auto.
  (* trans *)
  apply compare_trans.
 Qed.

 Instance lt_strorder : StrictOrder lt.
 Proof.
  split; repeat red; unfold lt; try apply compare_trans.
  intros x H.
  assert (eq x x) by reflexivity.
  unfold eq in *; congruence.
 Qed.

 Lemma lt_eq : forall x y z, lt x y -> eq y z -> lt x z.
 Proof.
  unfold lt, eq; intros x y z Hxy Hyz.
  destruct (compare x z) eqn:Hxz; auto.
  rewrite compare_sym, CompOpp_iff in Hyz. simpl in Hyz.
  rewrite (compare_trans Hxz Hyz) in Hxy; discriminate.
  rewrite compare_sym, CompOpp_iff in Hxy. simpl in Hxy.
  rewrite (compare_trans Hxy Hxz) in Hyz; discriminate.
 Qed.

 Lemma eq_lt : forall x y z, eq x y -> lt y z -> lt x z.
 Proof.
  unfold lt, eq; intros x y z Hxy Hyz.
  destruct (compare x z) eqn:Hxz; auto.
  rewrite compare_sym, CompOpp_iff in Hxy. simpl in Hxy.
  rewrite (compare_trans Hxy Hxz) in Hyz; discriminate.
  rewrite compare_sym, CompOpp_iff in Hyz. simpl in Hyz.
  rewrite (compare_trans Hxz Hyz) in Hxy; discriminate.
 Qed.

 Instance lt_compat : Proper (eq==>eq==>iff) lt.
 Proof.
  apply proper_sym_impl_iff_2; auto with *.
  repeat red; intros.
  eapply lt_eq; eauto. eapply eq_lt; eauto. symmetry; auto.
 Qed.

 Definition compare := O.compare.

 Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
 Proof.
  unfold eq, lt, compare; intros.
  destruct (O.compare x y) eqn:H; auto.
  apply CompGt.
  rewrite compare_sym, H; auto.
 Qed.

 Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
 Proof.
 intros; unfold eq.
 case (x ?= y); [ left | right | right ]; auto; discriminate.
 Defined.

End OT_from_Alt.

(** From the original presentation to this alternative one. *)

Module OT_to_Alt (Import O:OrderedType) <: OrderedTypeAlt.

 Definition t := t.
 Definition compare := compare.

 Infix "?=" := compare (at level 70, no associativity).

 Lemma compare_sym :
   forall x y, (y?=x) = CompOpp (x?=y).
 Proof.
 intros x y; unfold compare.
 destruct (compare_spec x y) as [U|U|U];
  destruct (compare_spec y x) as [V|V|V]; auto.
 rewrite U in V. elim (StrictOrder_Irreflexive y); auto.
 rewrite U in V. elim (StrictOrder_Irreflexive y); auto.
 rewrite V in U. elim (StrictOrder_Irreflexive x); auto.
 rewrite V in U. elim (StrictOrder_Irreflexive x); auto.
 rewrite V in U. elim (StrictOrder_Irreflexive x); auto.
 rewrite V in U. elim (StrictOrder_Irreflexive y); auto.
 Qed.

 Lemma compare_Eq : forall x y, compare x y = Eq <-> eq x y.
 Proof.
 unfold compare.
 intros x y; destruct (compare_spec x y); intuition;
  try discriminate.
 rewrite H0 in H. elim (StrictOrder_Irreflexive y); auto.
 rewrite H0 in H. elim (StrictOrder_Irreflexive y); auto.
 Qed.

 Lemma compare_Lt : forall x y, compare x y = Lt <-> lt x y.
 Proof.
 unfold compare.
 intros x y; destruct (compare_spec x y); intuition;
  try discriminate.
 rewrite H in H0. elim (StrictOrder_Irreflexive y); auto.
 rewrite H in H0. elim (StrictOrder_Irreflexive x); auto.
 Qed.

 Lemma compare_Gt : forall x y, compare x y = Gt <-> lt y x.
 Proof.
 intros x y. rewrite compare_sym, CompOpp_iff. apply compare_Lt.
 Qed.

 Lemma compare_trans :
   forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
 Proof.
 intros c x y z.
 destruct c; unfold compare;
  rewrite ?compare_Eq, ?compare_Lt, ?compare_Gt;
  transitivity y; auto.
 Qed.

End OT_to_Alt.
