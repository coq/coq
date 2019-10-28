(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Propositional operators known to [tify] tactics. *)
Require Import ZifyClasses.
Declare ML Module "zify_plugin".

(** Propositional logic *)
Instance PropAnd : PropOp and.
Proof.
  constructor.
  tauto.
Defined.
Add PropOp PropAnd.

Instance PropOr : PropOp or.
Proof.
  constructor.
  tauto.
Defined.
Add PropOp PropOr.

Instance PropArrow : PropOp (fun x y => x -> y).
Proof.
  constructor.
  intros.
  tauto.
Defined.
Add PropOp PropArrow.

Instance PropIff : PropOp iff.
Proof.
  constructor.
  intros.
  tauto.
Defined.
Add PropOp PropIff.

Instance PropNot : PropUOp not.
Proof.
  constructor.
  intros.
  tauto.
Defined.
Add PropUOp PropNot.
