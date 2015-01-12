(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Efficient arbitrary large natural numbers in base 2^31 *)

(** Initial Author: Arnaud Spiwack *)

Require Export Int31.
Require Import CyclicAxioms Cyclic31 Ring31 NSig NSigNAxioms NMake
  NProperties GenericMinMax.

(** The following [BigN] module regroups both the operations and
    all the abstract properties:

    - [NMake.Make Int31Cyclic] provides the operations and basic specs
       w.r.t. ZArith
    - [NTypeIsNAxioms] shows (mainly) that these operations implement
      the interface [NAxioms]
    - [NProp] adds all generic properties derived from [NAxioms]
    - [MinMax*Properties] provides properties of [min] and [max].

*)

Delimit Scope bigN_scope with bigN.

Module BigN <: NType <: OrderedTypeFull <: TotalOrder :=
  NMake.Make Int31Cyclic
  <+ NTypeIsNAxioms
  <+ NBasicProp [no inline] <+ NExtraProp [no inline]
  <+ HasEqBool2Dec [no inline]
  <+ MinMaxLogicalProperties [no inline]
  <+ MinMaxDecProperties [no inline].

(** Notations about [BigN] *)

Local Open Scope bigN_scope.

Notation bigN := BigN.t.
Bind Scope bigN_scope with bigN BigN.t BigN.t'.
Arguments BigN.N0 _%int31.
Local Notation "0" := BigN.zero : bigN_scope. (* temporary notation *)
Local Notation "1" := BigN.one : bigN_scope. (* temporary notation *)
Local Notation "2" := BigN.two : bigN_scope. (* temporary notation *)
Infix "+" := BigN.add : bigN_scope.
Infix "-" := BigN.sub : bigN_scope.
Infix "*" := BigN.mul : bigN_scope.
Infix "/" := BigN.div : bigN_scope.
Infix "^" := BigN.pow : bigN_scope.
Infix "?=" := BigN.compare : bigN_scope.
Infix "=?" := BigN.eqb (at level 70, no associativity) : bigN_scope.
Infix "<=?" := BigN.leb (at level 70, no associativity) : bigN_scope.
Infix "<?" := BigN.ltb (at level 70, no associativity) : bigN_scope.
Infix "==" := BigN.eq (at level 70, no associativity) : bigN_scope.
Notation "x != y" := (~x==y) (at level 70, no associativity) : bigN_scope.
Infix "<" := BigN.lt : bigN_scope.
Infix "<=" := BigN.le : bigN_scope.
Notation "x > y" := (y < x) (only parsing) : bigN_scope.
Notation "x >= y" := (y <= x) (only parsing) : bigN_scope.
Notation "x < y < z" := (x<y /\ y<z) : bigN_scope.
Notation "x < y <= z" := (x<y /\ y<=z) : bigN_scope.
Notation "x <= y < z" := (x<=y /\ y<z) : bigN_scope.
Notation "x <= y <= z" := (x<=y /\ y<=z) : bigN_scope.
Notation "[ i ]" := (BigN.to_Z i) : bigN_scope.
Infix "mod" := BigN.modulo (at level 40, no associativity) : bigN_scope.

(** Example of reasoning about [BigN] *)

Theorem succ_pred: forall q : bigN,
  0 < q -> BigN.succ (BigN.pred q) == q.
Proof.
intros; apply BigN.succ_pred.
intro H'; rewrite H' in H; discriminate.
Qed.

(** [BigN] is a semi-ring *)

Lemma BigNring : semi_ring_theory 0 1 BigN.add BigN.mul BigN.eq.
Proof.
constructor.
exact BigN.add_0_l. exact BigN.add_comm. exact BigN.add_assoc.
exact BigN.mul_1_l. exact BigN.mul_0_l. exact BigN.mul_comm.
exact BigN.mul_assoc. exact BigN.mul_add_distr_r.
Qed.

Lemma BigNeqb_correct : forall x y, (x =? y) = true -> x==y.
Proof. now apply BigN.eqb_eq. Qed.

Lemma BigNpower : power_theory 1 BigN.mul BigN.eq BigN.of_N BigN.pow.
Proof.
constructor.
intros. red. rewrite BigN.spec_pow, BigN.spec_of_N.
rewrite Zpower_theory.(rpow_pow_N).
destruct n; simpl. reflexivity.
induction p; simpl; intros; BigN.zify; rewrite ?IHp; auto.
Qed.

Lemma BigNdiv : div_theory BigN.eq BigN.add BigN.mul (@id _)
 (fun a b => if b =? 0 then (0,a) else BigN.div_eucl a b).
Proof.
constructor. unfold id. intros a b.
BigN.zify.
case Z.eqb_spec.
BigN.zify. auto with zarith.
intros NEQ.
generalize (BigN.spec_div_eucl a b).
generalize (Z_div_mod_full [a] [b] NEQ).
destruct BigN.div_eucl as (q,r), Z.div_eucl as (q',r').
intros (EQ,_). injection 1. intros EQr EQq.
BigN.zify. rewrite EQr, EQq; auto.
Qed.


(** Detection of constants *)

Ltac isStaticWordCst t :=
 match t with
 | W0 => constr:true
 | WW ?t1 ?t2 =>
   match isStaticWordCst t1 with
   | false => constr:false
   | true => isStaticWordCst t2
   end
 | _ => isInt31cst t
 end.

Ltac isBigNcst t :=
 match t with
 | BigN.N0 ?t => isStaticWordCst t
 | BigN.N1 ?t => isStaticWordCst t
 | BigN.N2 ?t => isStaticWordCst t
 | BigN.N3 ?t => isStaticWordCst t
 | BigN.N4 ?t => isStaticWordCst t
 | BigN.N5 ?t => isStaticWordCst t
 | BigN.N6 ?t => isStaticWordCst t
 | BigN.Nn ?n ?t => match isnatcst n with
   | true => isStaticWordCst t
   | false => constr:false
   end
 | BigN.zero => constr:true
 | BigN.one => constr:true
 | BigN.two => constr:true
 | _ => constr:false
 end.

Ltac BigNcst t :=
 match isBigNcst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

Ltac BigN_to_N t :=
 match isBigNcst t with
 | true => eval vm_compute in (BigN.to_N t)
 | false => constr:NotConstant
 end.

Ltac Ncst t :=
 match isNcst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

(** Registration for the "ring" tactic *)

Add Ring BigNr : BigNring
 (decidable BigNeqb_correct,
  constants [BigNcst],
  power_tac BigNpower [BigN_to_N],
  div BigNdiv).

Section TestRing.
Let test : forall x y, 1 + x*y^1 + x^2 + 1 == 1*1 + 1 + y*x + 1*x*x.
intros. ring_simplify. reflexivity.
Qed.
End TestRing.

(** We benefit also from an "order" tactic *)

Ltac bigN_order := BigN.order.

Section TestOrder.
Let test : forall x y : bigN, x<=y -> y<=x -> x==y.
Proof. bigN_order. Qed.
End TestOrder.

(** We can use at least a bit of (r)omega by translating to [Z]. *)

Section TestOmega.
Let test : forall x y : bigN, x<=y -> y<=x -> x==y.
Proof. intros x y. BigN.zify. omega. Qed.
End TestOmega.

(** Todo: micromega *)
