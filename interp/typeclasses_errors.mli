(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Environ

type typeclass_error =
  | NotAClass of constr
  | UnboundMethod of GlobRef.t * lident (** Class name, method *)

exception TypeClassError of env * Evd.evar_map * typeclass_error

val typeclass_error : env -> Evd.evar_map -> typeclass_error -> 'a

val not_a_class : env -> Evd.evar_map -> constr -> 'a

val unbound_method : env -> Evd.evar_map -> GlobRef.t -> lident -> 'a
