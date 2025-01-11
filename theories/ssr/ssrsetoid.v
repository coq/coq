(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** #<style> .doc { font-family: monospace; white-space: pre; } </style># **)

(** Compatibility layer for [under] and [setoid_rewrite].

 This file is intended to be required by [Require Import Setoid].

 In particular, we can use the [under] tactic with other relations
 than [eq] or [iff], e.g. a [RewriteRelation], by doing:
 [Require Import ssreflect. Require Setoid.]

 This file's instances have priority 12 > other stdlib instances.

 (Note: this file could be skipped when porting [under] to stdlib2.)
 *)

Require Import ssrclasses.
Require Import ssrunder.
Require Import RelationClasses.
Require Import Relation_Definitions.

(** Reconcile [Corelib.Classes.RelationClasses.Reflexive] with
    [Corelib.ssr.ssrclasses.Reflexive] *)

#[global]
Instance compat_Reflexive :
  forall {A} {R : relation A},
    RelationClasses.Reflexive R ->
    ssrclasses.Reflexive R | 12.
Proof. now trivial. Qed.
