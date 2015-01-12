(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Export BigN.
Require Import ZProperties ZDivFloor ZSig ZSigZAxioms ZMake.

(** * [BigZ] : arbitrary large efficient integers.

    The following [BigZ] module regroups both the operations and
    all the abstract properties:

    - [ZMake.Make BigN] provides the operations and basic specs w.r.t. ZArith
    - [ZTypeIsZAxioms] shows (mainly) that these operations implement
      the interface [ZAxioms]
    - [ZProp] adds all generic properties derived from [ZAxioms]
    - [MinMax*Properties] provides properties of [min] and [max]

*)

Delimit Scope bigZ_scope with bigZ.

Module BigZ <: ZType <: OrderedTypeFull <: TotalOrder :=
 ZMake.Make BigN
 <+ ZTypeIsZAxioms
 <+ ZBasicProp [no inline] <+ ZExtraProp [no inline]
 <+ HasEqBool2Dec [no inline]
 <+ MinMaxLogicalProperties [no inline]
 <+ MinMaxDecProperties [no inline].

(** For precision concerning the above scope handling, see comment in BigN *)

(** Notations about [BigZ] *)

Local Open Scope bigZ_scope.

Notation bigZ := BigZ.t.
Bind Scope bigZ_scope with bigZ BigZ.t BigZ.t_.
Arguments BigZ.Pos _%bigN.
Arguments BigZ.Neg _%bigN.
Local Notation "0" := BigZ.zero : bigZ_scope.
Local Notation "1" := BigZ.one : bigZ_scope.
Local Notation "2" := BigZ.two : bigZ_scope.
Infix "+" := BigZ.add : bigZ_scope.
Infix "-" := BigZ.sub : bigZ_scope.
Notation "- x" := (BigZ.opp x) : bigZ_scope.
Infix "*" := BigZ.mul : bigZ_scope.
Infix "/" := BigZ.div : bigZ_scope.
Infix "^" := BigZ.pow : bigZ_scope.
Infix "?=" := BigZ.compare : bigZ_scope.
Infix "=?" := BigZ.eqb (at level 70, no associativity) : bigZ_scope.
Infix "<=?" := BigZ.leb (at level 70, no associativity) : bigZ_scope.
Infix "<?" := BigZ.ltb (at level 70, no associativity) : bigZ_scope.
Infix "==" := BigZ.eq (at level 70, no associativity) : bigZ_scope.
Notation "x != y" := (~x==y) (at level 70, no associativity) : bigZ_scope.
Infix "<" := BigZ.lt : bigZ_scope.
Infix "<=" := BigZ.le : bigZ_scope.
Notation "x > y" := (y < x) (only parsing) : bigZ_scope.
Notation "x >= y" := (y <= x) (only parsing) : bigZ_scope.
Notation "x < y < z" := (x<y /\ y<z) : bigZ_scope.
Notation "x < y <= z" := (x<y /\ y<=z) : bigZ_scope.
Notation "x <= y < z" := (x<=y /\ y<z) : bigZ_scope.
Notation "x <= y <= z" := (x<=y /\ y<=z) : bigZ_scope.
Notation "[ i ]" := (BigZ.to_Z i) : bigZ_scope.
Infix "mod" := BigZ.modulo (at level 40, no associativity) : bigZ_scope.
Infix "÷" := BigZ.quot (at level 40, left associativity) : bigZ_scope.

(** Some additional results about [BigZ] *)

Theorem spec_to_Z: forall n : bigZ,
  BigN.to_Z (BigZ.to_N n) = ((Z.sgn [n]) * [n])%Z.
Proof.
intros n; case n; simpl; intros p;
  generalize (BigN.spec_pos p); case (BigN.to_Z p); auto.
intros p1 H1; case H1; auto.
intros p1 H1; case H1; auto.
Qed.

Theorem spec_to_N n:
 ([n] = Z.sgn [n] * (BigN.to_Z (BigZ.to_N n)))%Z.
Proof.
case n; simpl; intros p;
  generalize (BigN.spec_pos p); case (BigN.to_Z p); auto.
intros p1 H1; case H1; auto.
intros p1 H1; case H1; auto.
Qed.

Theorem spec_to_Z_pos: forall n, (0 <= [n])%Z ->
  BigN.to_Z (BigZ.to_N n) = [n].
Proof.
intros n; case n; simpl; intros p;
  generalize (BigN.spec_pos p); case (BigN.to_Z p); auto.
intros p1 _ H1; case H1; auto.
intros p1 H1; case H1; auto.
Qed.

(** [BigZ] is a ring *)

Lemma BigZring :
 ring_theory 0 1 BigZ.add BigZ.mul BigZ.sub BigZ.opp BigZ.eq.
Proof.
constructor.
exact BigZ.add_0_l. exact BigZ.add_comm. exact BigZ.add_assoc.
exact BigZ.mul_1_l. exact BigZ.mul_comm. exact BigZ.mul_assoc.
exact BigZ.mul_add_distr_r.
symmetry. apply BigZ.add_opp_r.
exact BigZ.add_opp_diag_r.
Qed.

Lemma BigZeqb_correct : forall x y, (x =? y) = true -> x==y.
Proof. now apply BigZ.eqb_eq. Qed.

Definition BigZ_of_N n := BigZ.of_Z (Z.of_N n).

Lemma BigZpower : power_theory 1 BigZ.mul BigZ.eq BigZ_of_N BigZ.pow.
Proof.
constructor.
intros. unfold BigZ.eq, BigZ_of_N. rewrite BigZ.spec_pow, BigZ.spec_of_Z.
rewrite Zpower_theory.(rpow_pow_N).
destruct n; simpl. reflexivity.
induction p; simpl; intros; BigZ.zify; rewrite ?IHp; auto.
Qed.

Lemma BigZdiv : div_theory BigZ.eq BigZ.add BigZ.mul (@id _)
 (fun a b => if b =? 0 then (0,a) else BigZ.div_eucl a b).
Proof.
constructor. unfold id. intros a b.
BigZ.zify.
case Z.eqb_spec.
BigZ.zify. auto with zarith.
intros NEQ.
generalize (BigZ.spec_div_eucl a b).
generalize (Z_div_mod_full [a] [b] NEQ).
destruct BigZ.div_eucl as (q,r), Z.div_eucl as (q',r').
intros (EQ,_). injection 1. intros EQr EQq.
BigZ.zify. rewrite EQr, EQq; auto.
Qed.

(** Detection of constants *)

Ltac isBigZcst t :=
 match t with
 | BigZ.Pos ?t => isBigNcst t
 | BigZ.Neg ?t => isBigNcst t
 | BigZ.zero => constr:true
 | BigZ.one => constr:true
 | BigZ.two => constr:true
 | BigZ.minus_one => constr:true
 | _ => constr:false
 end.

Ltac BigZcst t :=
 match isBigZcst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

Ltac BigZ_to_N t :=
 match t with
 | BigZ.Pos ?t => BigN_to_N t
 | BigZ.zero => constr:0%N
 | BigZ.one => constr:1%N
 | BigZ.two => constr:2%N
 | _ => constr:NotConstant
 end.

(** Registration for the "ring" tactic *)

Add Ring BigZr : BigZring
 (decidable BigZeqb_correct,
  constants [BigZcst],
  power_tac BigZpower [BigZ_to_N],
  div BigZdiv).

Section TestRing.
Let test : forall x y, 1 + x*y + x^2 + 1 == 1*1 + 1 + (y + 1*x)*x.
Proof.
intros. ring_simplify. reflexivity.
Qed.
Let test' : forall x y, 1 + x*y + x^2 - 1*1 - y*x + 1*(-x)*x == 0.
Proof.
intros. ring_simplify. reflexivity.
Qed.
End TestRing.

(** [BigZ] also benefits from an "order" tactic *)

Ltac bigZ_order := BigZ.order.

Section TestOrder.
Let test : forall x y : bigZ, x<=y -> y<=x -> x==y.
Proof. bigZ_order. Qed.
End TestOrder.

(** We can use at least a bit of (r)omega by translating to [Z]. *)

Section TestOmega.
Let test : forall x y : bigZ, x<=y -> y<=x -> x==y.
Proof. intros x y. BigZ.zify. omega. Qed.
End TestOmega.

(** Todo: micromega *)
