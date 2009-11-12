(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** * Natural numbers in base 2^31 *)

(**
Author: Arnaud Spiwack
*)

Require Export Int31.
Require Import CyclicAxioms.
Require Import Cyclic31.
Require Import NSig.
Require Import NSigNAxioms.
Require Import NMake.
Require Import NProperties.

Module BigN <: NType := NMake.Make Int31Cyclic.

(** Module [BigN] implements [NAxiomsSig] *)

Module Export BigNAxiomsMod := NSig_NAxioms BigN.
Module Export BigNPropMod := NPropFunct BigNAxiomsMod.

(** Notations about [BigN] *)

Notation bigN := BigN.t.

Delimit Scope bigN_scope with bigN.
Bind Scope bigN_scope with bigN.
Bind Scope bigN_scope with BigN.t.
Bind Scope bigN_scope with BigN.t_.
(* Bind Scope has no retroactive effect, let's declare scopes by hand. *)
Arguments Scope BigN.to_Z [bigN_scope].
Arguments Scope BigN.succ [bigN_scope].
Arguments Scope BigN.pred [bigN_scope].
Arguments Scope BigN.square [bigN_scope].
Arguments Scope BigN.add [bigN_scope bigN_scope].
Arguments Scope BigN.sub [bigN_scope bigN_scope].
Arguments Scope BigN.mul [bigN_scope bigN_scope].
Arguments Scope BigN.div [bigN_scope bigN_scope].
Arguments Scope BigN.eq [bigN_scope bigN_scope].
Arguments Scope BigN.lt [bigN_scope bigN_scope].
Arguments Scope BigN.le [bigN_scope bigN_scope].
Arguments Scope BigN.eq [bigN_scope bigN_scope].
Arguments Scope BigN.compare [bigN_scope bigN_scope].
Arguments Scope BigN.min [bigN_scope bigN_scope].
Arguments Scope BigN.max [bigN_scope bigN_scope].
Arguments Scope BigN.eq_bool [bigN_scope bigN_scope].
Arguments Scope BigN.power_pos [bigN_scope positive_scope].
Arguments Scope BigN.sqrt [bigN_scope].
Arguments Scope BigN.div_eucl [bigN_scope bigN_scope].
Arguments Scope BigN.modulo [bigN_scope bigN_scope].
Arguments Scope BigN.gcd [bigN_scope bigN_scope].

Local Notation "0" := BigN.zero : bigN_scope. (* temporary notation *)
Infix "+" := BigN.add : bigN_scope.
Infix "-" := BigN.sub : bigN_scope.
Infix "*" := BigN.mul : bigN_scope.
Infix "/" := BigN.div : bigN_scope.
Infix "^" := BigN.power_pos : bigN_scope.
Infix "?=" := BigN.compare : bigN_scope.
Infix "==" := BigN.eq (at level 70, no associativity) : bigN_scope.
Infix "<" := BigN.lt : bigN_scope.
Infix "<=" := BigN.le : bigN_scope.
Notation "x > y" := (BigN.lt y x)(only parsing) : bigN_scope.
Notation "x >= y" := (BigN.le y x)(only parsing) : bigN_scope.
Notation "[ i ]" := (BigN.to_Z i) : bigN_scope.

Local Open Scope bigN_scope.

(** Example of reasoning about [BigN] *)

Theorem succ_pred: forall q : bigN,
  0 < q -> BigN.succ (BigN.pred q) == q.
Proof.
intros; apply succ_pred.
intro H'; rewrite H' in H; discriminate.
Qed.

(** [BigN] is a semi-ring *)

Lemma BigNring :
 semi_ring_theory BigN.zero BigN.one BigN.add BigN.mul BigN.eq.
Proof.
constructor.
exact add_0_l.
exact add_comm.
exact add_assoc.
exact mul_1_l.
exact mul_0_l.
exact mul_comm.
exact mul_assoc.
exact mul_add_distr_r.
Qed.

Add Ring BigNr : BigNring.

(** Todo: tactic translating from [BigN] to [Z] + omega *)

(** Todo: micromega *)
