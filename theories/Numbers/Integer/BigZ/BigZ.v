(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
Arguments Scope BigZ.sqrt [bigZ_scope].
Arguments Scope BigZ.div_eucl [bigZ_scope bigZ_scope].
Arguments Scope BigZ.modulo [bigZ_scope bigZ_scope].
Arguments Scope BigZ.gcd [bigZ_scope bigZ_scope].

Local Notation "0" := BigZ.zero : bigZ_scope.
Infix "+" := BigZ.add : bigZ_scope.
Infix "-" := BigZ.sub : bigZ_scope.
Notation "- x" := (BigZ.opp x) : bigZ_scope.
Infix "*" := BigZ.mul : bigZ_scope.
Infix "/" := BigZ.div : bigZ_scope.
Infix "^" := BigZ.power_pos : bigZ_scope.
Infix "?=" := BigZ.compare : bigZ_scope.
Infix "==" := BigZ.eq (at level 70, no associativity) : bigZ_scope.
Infix "<" := BigZ.lt : bigZ_scope.
Infix "<=" := BigZ.le : bigZ_scope.
Notation "x > y" := (BigZ.lt y x)(only parsing) : bigZ_scope.
Notation "x >= y" := (BigZ.le y x)(only parsing) : bigZ_scope.
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
intros n; case n; simpl; intros p;
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
 ring_theory BigZ.zero BigZ.one BigZ.add BigZ.mul BigZ.sub BigZ.opp BigZ.eq.
Proof.
constructor.
exact BigZ.add_0_l.
exact BigZ.add_comm.
exact BigZ.add_assoc.
exact BigZ.mul_1_l.
exact BigZ.mul_comm.
exact BigZ.mul_assoc.
exact BigZ.mul_add_distr_r.
symmetry. apply BigZ.add_opp_r.
exact BigZ.add_opp_diag_r.
Qed.

Add Ring BigZr : BigZring.

(** [BigZ] benefits from an "order" tactic *)

Ltac bigZ_order := BigZ.order.

Section Test.
Let test : forall x y : bigZ, x<=y -> y<=x -> x==y.
Proof. bigZ_order. Qed.
End Test.

(** Todo: tactic translating from [BigZ] to [Z] + omega *)

(** Todo: micromega *)
