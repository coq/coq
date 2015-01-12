(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import QArith Qpower Qminmax Orders RelationPairs GenericMinMax.

Open Scope Q_scope.

(** * QSig *)

(** Interface of a rich structure about rational numbers.
    Specifications are written via translation to Q.
*)

Module Type QType.

 Parameter t : Type.

 Parameter to_Q : t -> Q.
 Local Notation "[ x ]" := (to_Q x).

 Definition eq x y := [x] == [y].
 Definition lt x y := [x] < [y].
 Definition le x y := [x] <= [y].

 Parameter of_Q : Q -> t.
 Parameter spec_of_Q: forall x, to_Q (of_Q x) == x.

 Parameter red : t -> t.
 Parameter compare : t -> t -> comparison.
 Parameter eq_bool : t -> t -> bool.
 Parameter max : t -> t -> t.
 Parameter min : t -> t -> t.
 Parameter zero : t.
 Parameter one : t.
 Parameter minus_one : t.
 Parameter add : t -> t -> t.
 Parameter sub : t -> t -> t.
 Parameter opp : t -> t.
 Parameter mul : t -> t -> t.
 Parameter square : t -> t.
 Parameter inv : t -> t.
 Parameter div : t -> t -> t.
 Parameter power : t -> Z -> t.

 Parameter spec_red : forall x, [red x] == [x].
 Parameter strong_spec_red : forall x, [red x] = Qred [x].
 Parameter spec_compare : forall x y, compare x y = ([x] ?= [y]).
 Parameter spec_eq_bool : forall x y, eq_bool x y = Qeq_bool [x] [y].
 Parameter spec_max : forall x y, [max x y] == Qmax [x] [y].
 Parameter spec_min : forall x y, [min x y] == Qmin [x] [y].
 Parameter spec_0: [zero] == 0.
 Parameter spec_1: [one] == 1.
 Parameter spec_m1: [minus_one] == -(1).
 Parameter spec_add: forall x y, [add x y] == [x] + [y].
 Parameter spec_sub: forall x y, [sub x y] == [x] - [y].
 Parameter spec_opp: forall x, [opp x] == - [x].
 Parameter spec_mul: forall x y, [mul x y] == [x] * [y].
 Parameter spec_square: forall x, [square x] == [x] ^ 2.
 Parameter spec_inv : forall x, [inv x] == / [x].
 Parameter spec_div: forall x y, [div x y] == [x] / [y].
 Parameter spec_power: forall x z, [power x z] == [x] ^ z.

End QType.

(** NB: several of the above functions come with [..._norm] variants
     that expect reduced arguments and return reduced results. *)

(** TODO : also speak of specifications via Qcanon ... *)

Module Type QType_Notation (Import Q : QType).
 Notation "[ x ]" := (to_Q x).
 Infix "=="  := eq (at level 70).
 Notation "x != y" := (~x==y) (at level 70).
 Infix "<=" := le.
 Infix "<" := lt.
 Notation "0" := zero.
 Notation "1" := one.
 Infix "+" := add.
 Infix "-" := sub.
 Infix "*" := mul.
 Notation "- x" := (opp x).
 Infix "/" := div.
 Notation "/ x" := (inv x).
 Infix "^" := power.
End QType_Notation.

Module Type QType' := QType <+ QType_Notation.


Module QProperties (Import Q : QType').

(** Conversion to Q *)

Hint Rewrite
 spec_red spec_compare spec_eq_bool spec_min spec_max
 spec_add spec_sub spec_opp spec_mul spec_square spec_inv spec_div
 spec_power : qsimpl.
Ltac qify := unfold eq, lt, le in *; autorewrite with qsimpl;
 try rewrite spec_0 in *; try rewrite spec_1 in *; try rewrite spec_m1 in *.

(** NB: do not add [spec_0] in the autorewrite database. Otherwise,
    after instantiation in BigQ, this lemma become convertible to 0=0,
    and autorewrite loops. Idem for [spec_1] and [spec_m1] *)

(** Morphisms *)

Ltac solve_wd1 := intros x x' Hx; qify; now rewrite Hx.
Ltac solve_wd2 := intros x x' Hx y y' Hy; qify; now rewrite Hx, Hy.

Local Obligation Tactic := solve_wd2 || solve_wd1.

Instance : Measure to_Q.
Instance eq_equiv : Equivalence eq := {}.

Program Instance lt_wd : Proper (eq==>eq==>iff) lt.
Program Instance le_wd : Proper (eq==>eq==>iff) le.
Program Instance red_wd : Proper (eq==>eq) red.
Program Instance compare_wd : Proper (eq==>eq==>Logic.eq) compare.
Program Instance eq_bool_wd : Proper (eq==>eq==>Logic.eq) eq_bool.
Program Instance min_wd : Proper (eq==>eq==>eq) min.
Program Instance max_wd : Proper (eq==>eq==>eq) max.
Program Instance add_wd : Proper (eq==>eq==>eq) add.
Program Instance sub_wd : Proper (eq==>eq==>eq) sub.
Program Instance opp_wd : Proper (eq==>eq) opp.
Program Instance mul_wd : Proper (eq==>eq==>eq) mul.
Program Instance square_wd : Proper (eq==>eq) square.
Program Instance inv_wd : Proper (eq==>eq) inv.
Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance power_wd : Proper (eq==>Logic.eq==>eq) power.

(** Let's implement [HasCompare] *)

Lemma compare_spec : forall x y, CompareSpec (x==y) (x<y) (y<x) (compare x y).
Proof. intros. qify. destruct (Qcompare_spec [x] [y]); auto. Qed.

(** Let's implement [TotalOrder] *)

Definition lt_compat := lt_wd.
Instance lt_strorder : StrictOrder lt := {}.

Lemma le_lteq : forall x y, x<=y <-> x<y \/ x==y.
Proof. intros. qify. apply Qle_lteq. Qed.

Lemma lt_total : forall x y, x<y \/ x==y \/ y<x.
Proof. intros. destruct (compare_spec x y); auto. Qed.

(** Let's implement [HasEqBool] *)

Definition eqb := eq_bool.

Lemma eqb_eq : forall x y, eq_bool x y = true <-> x == y.
Proof. intros. qify. apply Qeq_bool_iff. Qed.

Lemma eqb_correct : forall x y, eq_bool x y = true -> x == y.
Proof. now apply eqb_eq. Qed.

Lemma eqb_complete : forall x y, x == y -> eq_bool x y = true.
Proof. now apply eqb_eq. Qed.

(** Let's implement [HasMinMax] *)

Lemma max_l : forall x y, y<=x -> max x y == x.
Proof. intros x y. qify. apply Qminmax.Q.max_l. Qed.

Lemma max_r : forall x y, x<=y -> max x y == y.
Proof. intros x y. qify. apply Qminmax.Q.max_r. Qed.

Lemma min_l : forall x y, x<=y -> min x y == x.
Proof. intros x y. qify. apply Qminmax.Q.min_l. Qed.

Lemma min_r : forall x y, y<=x -> min x y == y.
Proof. intros x y. qify. apply Qminmax.Q.min_r. Qed.

(** Q is a ring *)

Lemma add_0_l : forall x, 0+x == x.
Proof. intros. qify. apply Qplus_0_l. Qed.

Lemma add_comm : forall x y, x+y == y+x.
Proof. intros. qify. apply Qplus_comm. Qed.

Lemma add_assoc : forall x y z, x+(y+z) == x+y+z.
Proof. intros. qify. apply Qplus_assoc. Qed.

Lemma mul_1_l : forall x, 1*x == x.
Proof. intros. qify. apply Qmult_1_l. Qed.

Lemma mul_comm : forall x y, x*y == y*x.
Proof. intros. qify. apply Qmult_comm. Qed.

Lemma mul_assoc : forall x y z, x*(y*z) == x*y*z.
Proof. intros. qify. apply Qmult_assoc. Qed.

Lemma mul_add_distr_r : forall x y z, (x+y)*z == x*z + y*z.
Proof. intros. qify. apply Qmult_plus_distr_l. Qed.

Lemma sub_add_opp : forall x y, x-y == x+(-y).
Proof. intros. qify. now unfold Qminus. Qed.

Lemma add_opp_diag_r : forall x, x+(-x) == 0.
Proof. intros. qify. apply Qplus_opp_r. Qed.

(** Q is a field *)

Lemma neq_1_0 : 1!=0.
Proof. intros. qify. apply Q_apart_0_1. Qed.

Lemma div_mul_inv : forall x y, x/y == x*(/y).
Proof. intros. qify. now unfold Qdiv. Qed.

Lemma mul_inv_diag_l : forall x, x!=0 -> /x * x == 1.
Proof. intros x. qify. rewrite Qmult_comm. apply Qmult_inv_r. Qed.

End QProperties.

Module QTypeExt (Q : QType)
 <: QType <: TotalOrder <: HasCompare Q <: HasMinMax Q <: HasEqBool Q
 := Q <+ QProperties.
