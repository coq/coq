(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

Require Export BigN.
Require Import ZProperties ZDivFloor ZSig ZSigZAxioms ZMake.

(** * [BigZ] : arbitrary large efficient integers.

    The following [BigZ] module regroups both the operations and
    all the abstract properties:

    - [ZMake.Make BigN] provides the operations and basic specs w.r.t. ZArith
    - [ZTypeIsZAxioms] shows (mainly) that these operations implement
      the interface [ZAxioms]
    - [ZPropSig] adds all generic properties derived from [ZAxioms]
    - [ZDivPropFunct] provides generic properties of [div] and [mod]
      ("Floor" variant)
    - [MinMax*Properties] provides properties of [min] and [max]

*)


Module BigZ <: ZType <: OrderedTypeFull <: TotalOrder :=
 ZMake.Make BigN <+ ZTypeIsZAxioms
 <+ !ZPropSig <+ !ZDivPropFunct <+ HasEqBool2Dec
 <+ !MinMaxLogicalProperties <+ !MinMaxDecProperties.

(** Notations about [BigZ] *)

Notation bigZ := BigZ.t.

Delimit Scope bigZ_scope with bigZ.
Bind Scope bigZ_scope with bigZ.
Bind Scope bigZ_scope with BigZ.t.
Bind Scope bigZ_scope with BigZ.t_.
(* Bind Scope has no retroactive effect, let's declare scopes by hand. *)
Arguments Scope BigZ.Pos [bigN_scope].
Arguments Scope BigZ.Neg [bigN_scope].
Arguments Scope BigZ.to_Z [bigZ_scope].
Arguments Scope BigZ.succ [bigZ_scope].
Arguments Scope BigZ.pred [bigZ_scope].
Arguments Scope BigZ.opp [bigZ_scope].
Arguments Scope BigZ.square [bigZ_scope].
Arguments Scope BigZ.add [bigZ_scope bigZ_scope].
Arguments Scope BigZ.sub [bigZ_scope bigZ_scope].
Arguments Scope BigZ.mul [bigZ_scope bigZ_scope].
Arguments Scope BigZ.div [bigZ_scope bigZ_scope].
Arguments Scope BigZ.eq [bigZ_scope bigZ_scope].
Arguments Scope BigZ.lt [bigZ_scope bigZ_scope].
Arguments Scope BigZ.le [bigZ_scope bigZ_scope].
Arguments Scope BigZ.eq [bigZ_scope bigZ_scope].
Arguments Scope BigZ.compare [bigZ_scope bigZ_scope].
Arguments Scope BigZ.min [bigZ_scope bigZ_scope].
Arguments Scope BigZ.max [bigZ_scope bigZ_scope].
Arguments Scope BigZ.eq_bool [bigZ_scope bigZ_scope].
Arguments Scope BigZ.power_pos [bigZ_scope positive_scope].
Arguments Scope BigZ.power [bigZ_scope N_scope].
Arguments Scope BigZ.sqrt [bigZ_scope].
Arguments Scope BigZ.div_eucl [bigZ_scope bigZ_scope].
Arguments Scope BigZ.modulo [bigZ_scope bigZ_scope].
Arguments Scope BigZ.gcd [bigZ_scope bigZ_scope].

Local Notation "0" := BigZ.zero : bigZ_scope.
Local Notation "1" := BigZ.one : bigZ_scope.
Infix "+" := BigZ.add : bigZ_scope.
Infix "-" := BigZ.sub : bigZ_scope.
Notation "- x" := (BigZ.opp x) : bigZ_scope.
Infix "*" := BigZ.mul : bigZ_scope.
Infix "/" := BigZ.div : bigZ_scope.
Infix "^" := BigZ.power : bigZ_scope.
Infix "?=" := BigZ.compare : bigZ_scope.
Infix "==" := BigZ.eq (at level 70, no associativity) : bigZ_scope.
Notation "x != y" := (~x==y)%bigZ (at level 70, no associativity) : bigZ_scope.
Infix "<" := BigZ.lt : bigZ_scope.
Infix "<=" := BigZ.le : bigZ_scope.
Notation "x > y" := (BigZ.lt y x)(only parsing) : bigZ_scope.
Notation "x >= y" := (BigZ.le y x)(only parsing) : bigZ_scope.
Notation "x < y < z" := (x<y /\ y<z)%bigZ : bigZ_scope.
Notation "x < y <= z" := (x<y /\ y<=z)%bigZ : bigZ_scope.
Notation "x <= y < z" := (x<=y /\ y<z)%bigZ : bigZ_scope.
Notation "x <= y <= z" := (x<=y /\ y<=z)%bigZ : bigZ_scope.
Notation "[ i ]" := (BigZ.to_Z i) : bigZ_scope.
Infix "mod" := BigZ.modulo (at level 40, no associativity) : bigN_scope.

Local Open Scope bigZ_scope.

(** Some additional results about [BigZ] *)

Theorem spec_to_Z: forall n : bigZ,
  BigN.to_Z (BigZ.to_N n) = ((Zsgn [n]) * [n])%Z.
Proof.
intros n; case n; simpl; intros p;
  generalize (BigN.spec_pos p); case (BigN.to_Z p); auto.
intros p1 H1; case H1; auto.
intros p1 H1; case H1; auto.
Qed.

Theorem spec_to_N n:
 ([n] = Zsgn [n] * (BigN.to_Z (BigZ.to_N n)))%Z.
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

Lemma BigZeqb_correct : forall x y, BigZ.eq_bool x y = true -> x==y.
Proof. now apply BigZ.eqb_eq. Qed.

Lemma BigZpower : power_theory 1 BigZ.mul BigZ.eq (@id N) BigZ.power.
Proof.
constructor.
intros. red. rewrite BigZ.spec_power. unfold id.
destruct Zpower_theory as [EQ]. rewrite EQ.
destruct n; simpl. reflexivity.
induction p; simpl; intros; BigZ.zify; rewrite ?IHp; auto.
Qed.

Lemma BigZdiv : div_theory BigZ.eq BigZ.add BigZ.mul (@id _)
 (fun a b => if BigZ.eq_bool b 0 then (0,a) else BigZ.div_eucl a b).
Proof.
constructor. unfold id. intros a b.
BigZ.zify.
generalize (Zeq_bool_if [b] 0); destruct (Zeq_bool [b] 0).
BigZ.zify. auto with zarith.
intros NEQ.
generalize (BigZ.spec_div_eucl a b).
generalize (Z_div_mod_full [a] [b] NEQ).
destruct BigZ.div_eucl as (q,r), Zdiv_eucl as (q',r').
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
 | BigZ.minus_one => constr:true
 | _ => constr:false
 end.

Ltac BigZcst t :=
 match isBigZcst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

(** Registration for the "ring" tactic *)

Add Ring BigZr : BigZring
 (decidable BigZeqb_correct,
  constants [BigZcst],
  power_tac BigZpower [Ncst],
  div BigZdiv).

Section TestRing.
Let test : forall x y, 1 + x*y + x^2 + 1 == 1*1 + 1 + y*x + 1*x*x.
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
