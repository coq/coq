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

Require Import OrderedType2.
Set Implicit Arguments.

(** NB: Instead of [comparison], defined in [Datatypes.v] which is [Eq|Lt|Gt],
  we used historically the dependent type [compare] which is
  [EQ _ | LT _ | GT _ ]
*)

Inductive Compare (X : Type) (lt eq : X -> X -> Prop) (x y : X) : Type :=
  | LT : lt x y -> Compare lt eq x y
  | EQ : eq x y -> Compare lt eq x y
  | GT : lt y x -> Compare lt eq x y.

(** * Some alternative (but equivalent) presentations for an Ordered Type
   inferface. *)

(** ** The original interface *)

Module Type OrderedTypeOrig.
  Parameter Inline t : Type.

  Parameter Inline eq : t -> t -> Prop.
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

  Parameter Inline lt : t -> t -> Prop.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, Compare lt eq x y.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans.

End OrderedTypeOrig.

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

Module OrderedType_from_Orig (O:OrderedTypeOrig) <: OrderedType.

 Import O.
 Definition t := O.t.
 Definition eq := O.eq.
 Instance eq_equiv : Equivalence eq.
 Proof.
  split; red; [ apply eq_refl | apply eq_sym | eapply eq_trans ].
 Qed.

 Definition lt := O.lt.
 Instance lt_strorder : StrictOrder lt.
 Proof.
  split; repeat red; intros.
  eapply lt_not_eq; eauto.
  eapply lt_trans; eauto.
 Qed.

 Lemma lt_eq : forall x y z, lt x y -> eq y z -> lt x z.
 Proof.
  intros; destruct (compare x z); auto.
  elim (@lt_not_eq x y); eauto.
  elim (@lt_not_eq z y); eauto using lt_trans.
 Qed.

 Lemma eq_lt : forall x y z, eq x y -> lt y z -> lt x z.
 Proof.
  intros; destruct (compare x z); auto.
  elim (@lt_not_eq y z); eauto.
  elim (@lt_not_eq y x); eauto using lt_trans.
 Qed.

 Instance lt_compat : Proper (eq==>eq==>iff) lt.
 Proof.
  apply proper_sym_impl_iff_2; auto with *.
  repeat red; intros.
  eapply lt_eq; eauto. eapply eq_lt; eauto. symmetry; auto.
 Qed.

 Definition compare x y :=
   match O.compare x y with
    | EQ _ => Eq
    | LT _ => Lt
    | GT _ => Gt
  end.

 Lemma compare_spec : forall x y, Cmp eq lt (compare x y) x y.
 Proof.
  intros; unfold compare; destruct O.compare; auto.
 Qed.

 Definition eq_dec : forall x y, { eq x y } + { ~eq x y }.
 Proof.
  intros; destruct (O.compare x y).
  right. apply lt_not_eq; auto.
  left; auto.
  right. intro. apply (@lt_not_eq y x); auto.
 Defined.

End OrderedType_from_Orig.

(** ** From OrderedType to OrderedTypeOrig. *)

Module OrderedType_to_Orig (O:OrderedType) <: OrderedTypeOrig.

 Import O.
 Definition t := t.
 Definition eq := eq.
 Definition lt := lt.

 Lemma eq_refl : Reflexive eq.
 Proof. auto. Qed.
 Lemma eq_sym : Symmetric eq.
 Proof. apply eq_equiv. Qed.
 Lemma eq_trans : Transitive eq.
 Proof. apply eq_equiv. Qed.

 Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
 Proof.
  intros x y L E; rewrite E in L. apply (StrictOrder_Irreflexive y); auto.
 Qed.

 Lemma lt_trans : Transitive lt.
 Proof. apply lt_strorder. Qed.

 Definition compare : forall x y, Compare lt eq x y.
 Proof.
  intros. generalize (compare_spec x y); unfold Cmp, flip.
  destruct (compare x y); [apply EQ|apply LT|apply GT]; auto.
 Defined.

 Definition eq_dec := eq_dec.

End OrderedType_to_Orig.


(** ** From OrderedTypeAlt to OrderedType. *)

Module OrderedType_from_Alt (O:OrderedTypeAlt) <: OrderedType.
 Import O.

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
  destruct (compare x z) as [ ]_eqn:Hxz; auto.
  rewrite compare_sym, CompOpp_iff in Hyz. simpl in Hyz.
  rewrite (compare_trans Hxz Hyz) in Hxy; discriminate.
  rewrite compare_sym, CompOpp_iff in Hxy. simpl in Hxy.
  rewrite (compare_trans Hxy Hxz) in Hyz; discriminate.
 Qed.

 Lemma eq_lt : forall x y z, eq x y -> lt y z -> lt x z.
 Proof.
  unfold lt, eq; intros x y z Hxy Hyz.
  destruct (compare x z) as [ ]_eqn:Hxz; auto.
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

 Lemma compare_spec : forall x y, Cmp eq lt (compare x y) x y.
 Proof.
  unfold Cmp, flip, eq, lt, compare; intros.
  destruct (O.compare x y) as [ ]_eqn:H; auto.
  rewrite compare_sym, H; auto.
 Qed.

 Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
 Proof.
 intros; unfold eq.
 case (x ?= y); [ left | right | right ]; auto; discriminate.
 Defined.

End OrderedType_from_Alt.

(** From the original presentation to this alternative one. *)

Module OrderedType_to_Alt (O:OrderedType) <: OrderedTypeAlt.
 Import O.

 Definition t := t.
 Definition compare := compare.

 Infix "?=" := compare (at level 70, no associativity).

 Lemma compare_sym :
   forall x y, (y?=x) = CompOpp (x?=y).
 Proof.
 intros x y; unfold compare.
 generalize (compare_spec x y) (compare_spec y x); unfold Cmp, flip.
 destruct (O.compare x y); destruct (O.compare y x); intros U V; auto.
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
 intros x y; generalize (compare_spec x y).
 destruct (O.compare x y); intuition; try discriminate.
 rewrite H0 in H. elim (StrictOrder_Irreflexive y); auto.
 rewrite H0 in H. elim (StrictOrder_Irreflexive y); auto.
 Qed.

 Lemma compare_Lt : forall x y, compare x y = Lt <-> lt x y.
 Proof.
 unfold compare.
 intros x y; generalize (compare_spec x y); unfold Cmp, flip.
 destruct (O.compare x y); intuition; try discriminate.
 rewrite H in H0. elim (StrictOrder_Irreflexive y); auto.
 rewrite H in H0. elim (StrictOrder_Irreflexive x); auto.
 Qed.

 Lemma compare_trans :
   forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
 Proof.
 intros c x y z.
 destruct c; unfold compare.
 rewrite 3 compare_Eq; eauto.
 rewrite 3 compare_Lt. apply StrictOrder_Transitive.
 do 3 (rewrite compare_sym, CompOpp_iff, compare_Lt).
 intros; apply StrictOrder_Transitive with y; auto.
 Qed.

End OrderedType_to_Alt.
