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
Require Import ZProperties.
Require Import ZSig.
Require Import ZSigZAxioms.
Require Import ZMake.

Module BigZ <: ZType := ZMake.Make BigN.

(** Module [BigZ] implements [ZAxiomsSig] *)

Module Export BigZAxiomsMod := ZSig_ZAxioms BigZ.
Module Export BigZPropMod := ZPropFunct BigZAxiomsMod.

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

Lemma sub_opp : forall x y : bigZ, x - y == x + (- y).
Proof.
red; intros; zsimpl; auto.
Qed.

Lemma add_opp : forall x : bigZ, x + (- x) == 0.
Proof.
red; intros; zsimpl; auto with zarith.
Qed.

(** [BigZ] is a ring *)

Lemma BigZring :
 ring_theory BigZ.zero BigZ.one BigZ.add BigZ.mul BigZ.sub BigZ.opp BigZ.eq.
Proof.
constructor.
exact add_0_l.
exact add_comm.
exact add_assoc.
exact mul_1_l.
exact mul_comm.
exact mul_assoc.
exact mul_add_distr_r.
exact sub_opp.
exact add_opp.
Qed.

Add Ring BigZr : BigZring.

(** Todo: tactic translating from [BigZ] to [Z] + omega *)

(** Todo: micromega *)
