(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * BigQ: an efficient implementation of rational numbers *)

(** Initial authors: Benjamin Gregoire, Laurent Thery, INRIA, 2007 *)

Require Export BigZ.
Require Import Field Qfield QSig QMake Orders GenericMinMax.

(** We choose for BigQ an implemention with
    multiple representation of 0: 0, 1/0, 2/0 etc.
    See [QMake.v] *)

(** First, we provide translations functions between [BigN] and [BigZ] *)

Module BigN_BigZ <: NType_ZType BigN.BigN BigZ.
 Definition Z_of_N := BigZ.Pos.
 Lemma spec_Z_of_N : forall n, BigZ.to_Z (Z_of_N n) = BigN.to_Z n.
 Proof.
 reflexivity.
 Qed.
 Definition Zabs_N := BigZ.to_N.
 Lemma spec_Zabs_N : forall z, BigN.to_Z (Zabs_N z) = Z.abs (BigZ.to_Z z).
 Proof.
 unfold Zabs_N; intros.
 rewrite BigZ.spec_to_Z, Z.mul_comm; apply Z.sgn_abs.
 Qed.
End BigN_BigZ.

(** This allows building [BigQ] out of [BigN] and [BigQ] via [QMake] *)

Delimit Scope bigQ_scope with bigQ.

Module BigQ <: QType <: OrderedTypeFull <: TotalOrder.
 Include QMake.Make BigN BigZ BigN_BigZ
  <+ !QProperties <+ HasEqBool2Dec
  <+ !MinMaxLogicalProperties <+ !MinMaxDecProperties.
 Ltac order := Private_Tac.order.
End BigQ.

(** Notations about [BigQ] *)

Local Open Scope bigQ_scope.

Notation bigQ := BigQ.t.
Bind Scope bigQ_scope with bigQ BigQ.t BigQ.t_.
(** As in QArith, we use [#] to denote fractions *)
Notation "p # q" := (BigQ.Qq p q) (at level 55, no associativity) : bigQ_scope.
Local Notation "0" := BigQ.zero : bigQ_scope.
Local Notation "1" := BigQ.one : bigQ_scope.
Infix "+" := BigQ.add : bigQ_scope.
Infix "-" := BigQ.sub : bigQ_scope.
Notation "- x" := (BigQ.opp x) : bigQ_scope.
Infix "*" := BigQ.mul : bigQ_scope.
Infix "/" := BigQ.div : bigQ_scope.
Infix "^" := BigQ.power : bigQ_scope.
Infix "?=" := BigQ.compare : bigQ_scope.
Infix "==" := BigQ.eq : bigQ_scope.
Notation "x != y" := (~x==y) (at level 70, no associativity) : bigQ_scope.
Infix "<" := BigQ.lt : bigQ_scope.
Infix "<=" := BigQ.le : bigQ_scope.
Notation "x > y" := (BigQ.lt y x) (only parsing) : bigQ_scope.
Notation "x >= y" := (BigQ.le y x) (only parsing) : bigQ_scope.
Notation "x < y < z" := (x<y /\ y<z) : bigQ_scope.
Notation "x < y <= z" := (x<y /\ y<=z) : bigQ_scope.
Notation "x <= y < z" := (x<=y /\ y<z) : bigQ_scope.
Notation "x <= y <= z" := (x<=y /\ y<=z) : bigQ_scope.
Notation "[ q ]" := (BigQ.to_Q q) : bigQ_scope.

(** [BigQ] is a field *)

Lemma BigQfieldth :
 field_theory 0 1 BigQ.add BigQ.mul BigQ.sub BigQ.opp
  BigQ.div BigQ.inv BigQ.eq.
Proof.
constructor.
constructor.
exact BigQ.add_0_l. exact BigQ.add_comm. exact BigQ.add_assoc.
exact BigQ.mul_1_l. exact BigQ.mul_comm. exact BigQ.mul_assoc.
exact BigQ.mul_add_distr_r. exact BigQ.sub_add_opp.
exact BigQ.add_opp_diag_r. exact BigQ.neq_1_0.
exact BigQ.div_mul_inv. exact BigQ.mul_inv_diag_l.
Qed.

Declare Equivalent Keys pow_N pow_pos.

Lemma BigQpowerth :
 power_theory 1 BigQ.mul BigQ.eq Z.of_N BigQ.power.
Proof.
constructor. intros. BigQ.qify.
replace ([r] ^ Z.of_N n)%Q with (pow_N 1 Qmult [r] n)%Q by (now destruct n).
destruct n. reflexivity.
induction p; simpl; auto; rewrite ?BigQ.spec_mul, ?IHp; reflexivity.
Qed.

Ltac isBigQcst t :=
 match t with
 | BigQ.Qz ?t => isBigZcst t
 | BigQ.Qq ?n ?d => match isBigZcst n with
             | true => isBigNcst d
             | false => constr:false
             end
 | BigQ.zero => constr:true
 | BigQ.one => constr:true
 | BigQ.minus_one => constr:true
 | _ => constr:false
 end.

Ltac BigQcst t :=
 match isBigQcst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

Add Field BigQfield : BigQfieldth
 (decidable BigQ.eqb_correct,
  completeness BigQ.eqb_complete,
  constants [BigQcst],
  power_tac BigQpowerth [Qpow_tac]).

Section TestField.

Let ex1 : forall x y z, (x+y)*z ==  (x*z)+(y*z).
  intros.
  ring.
Qed.

Let ex8 : forall x, x ^ 2 == x*x.
  intro.
  ring.
Qed.

Let ex10 : forall x y, y!=0 -> (x/y)*y == x.
intros.
field.
auto.
Qed.

End TestField.

(** [BigQ] can also benefit from an "order" tactic *)

Ltac bigQ_order := BigQ.order.

Section TestOrder.
Let test : forall x y : bigQ, x<=y -> y<=x -> x==y.
Proof. bigQ_order. Qed.
End TestOrder.

(** We can also reason by switching to QArith thanks to tactic
    BigQ.qify. *)

Section TestQify.
Let test : forall x : bigQ, 0+x == 1*x.
Proof. intro x. BigQ.qify. ring. Qed.
End TestQify.
