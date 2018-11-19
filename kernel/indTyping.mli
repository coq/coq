(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ

val typecheck_inductive :
  env ->
  Entries.mutual_inductive_entry ->
  env * env * rel_context *
  (Id.t * Id.t list * types array *
   (rel_context *
    (bool * types * Univ.Universe.t,
     Univ.Level.t option list * Univ.Universe.t)
      Declarations.declaration_arity))
    array
