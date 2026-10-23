(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export ssreflect_rw.
Declare ML Module "rocq-runtime.plugins.ssreflect_rewrite".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SsrIsSyntax.

(** Declare Ssr keywords: "is" "isn't". **)
Reserved Notation "(******* x 'is' y 'isn't' *******)".

End SsrIsSyntax.

Export SsrIsSyntax.

(** Signal that we have ssreflect version of rewrite (meaning
 "rewrite a" must be printed "rewrite -> a" for compatibility). **)
#[export] Set SSRRewriteLoaded.

(** Save primitive notation that will be overloaded. **)
Local Abbreviation RocqGenericIf c vT vF :=
  (if c then vT else vF) (only parsing).
Local Abbreviation RocqGenericDependentIf c x R vT vF :=
  (if c as x return R then vT else vF) (only parsing).

(** Reserve notations that are introduced in this file. **)
Reserved Notation "'if' c 'then' vT 'else' vF" (at level 10,
  c, vT, vF at level 200).
Reserved Notation "'if' c 'return' R 'then' vT 'else' vF" (at level 10,
  c, R, vT, vF at level 200).
Reserved Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" (at level 10,
  c, R, vT, vF at level 200, x name).

(**
 Make the general "if" into a notation, so that we can override it below.
 The notations are "only parsing" because the Rocq decompiler will not
 recognize the expansion of the boolean if; using the default printer
 avoids a spurious trailing %%GEN_IF. **)

Declare Scope general_if_scope.
Delimit Scope general_if_scope with GEN_IF.

Notation "'if' c 'then' vT 'else' vF" :=
  (RocqGenericIf c vT vF) (only parsing) : general_if_scope.

Notation "'if' c 'return' R 'then' vT 'else' vF" :=
  (RocqGenericDependentIf c c R vT vF) (only parsing) : general_if_scope.

Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" :=
  (RocqGenericDependentIf c x R vT vF) (only parsing) : general_if_scope.

(**  Force boolean interpretation of simple if expressions.  **)

Declare Scope boolean_if_scope.
Delimit Scope boolean_if_scope with BOOL_IF.

Notation "'if' c 'return' R 'then' vT 'else' vF" :=
  (if c is true as c in bool return R then vT else vF) : boolean_if_scope.

Notation "'if' c 'then' vT 'else' vF" :=
  (if c%bool is true as _ in bool return _ then vT else vF) : boolean_if_scope.

Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" :=
  (if c%bool is true as x in bool return R then vT else vF) : boolean_if_scope.

Open Scope boolean_if_scope.

(* This abbreviation is only parsing in Prelude *)
Abbreviation unkeyed x := (let flex := x in flex).

Abbreviation phant := ssreflect_rw.phant.
Abbreviation Phant := ssreflect_rw.Phant.
Abbreviation phantom := ssreflect_rw.phantom.
Abbreviation Phantom := ssreflect_rw.Phantom.
