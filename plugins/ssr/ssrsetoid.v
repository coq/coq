(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** #<style> .doc { font-family: monospace; white-space: pre; } </style># **)

(** Compatibility layer for [under] and [setoid_rewrite].

 This file is intended to be required by [Require Import Setoid] or so
 in order to reconcile [Coq.Classes.RelationClasses.Reflexive] with
 [Coq.ssr.ssrclasses.Reflexive].

 We can thus use the [under] tactic with other relations than [eq],
 such as [iff] or a [RewriteRelation], by doing:
 [Require Import ssreflect. Require Setoid.]

 (Note: this file could be skipped when porting [under] to stdlib2.)
 *)

Require Import ssrclasses.
Require Import RelationClasses.

Instance compat_Reflexive :
  forall {A} {R : A -> A -> Prop},
    RelationClasses.Reflexive R ->
    ssrclasses.Reflexive R.
Proof. now trivial. Qed.
