(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** We can take advantage of non-cumulativity of SProp to avoid fully
   retyping terms when we just want to know if they inhabit some
   proof-irrelevant type. *)

val relevance_of_term : Environ.env -> Constr.constr -> Sorts.relevance

val relevance_of_fterm : Environ.env -> Sorts.relevance list ->
  Esubst.lift -> CClosure.fconstr ->
  Sorts.relevance


(** Helpers *)
open Names
val relevance_of_rel_extra : Environ.env -> Sorts.relevance list -> int -> Sorts.relevance
val relevance_of_var : Environ.env -> Id.t -> Sorts.relevance
val relevance_of_constant : Environ.env -> Constant.t -> Sorts.relevance
val relevance_of_constructor : Environ.env -> constructor -> Sorts.relevance
val relevance_of_projection : Environ.env -> Projection.t -> Sorts.relevance
