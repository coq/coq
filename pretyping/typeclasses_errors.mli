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
  | NotATypeclass of constr
  | UnboundMethod of GlobRef.t * lident (** Class name, method *)

type _ CErrors.tag += TypeClassError : (env * Evd.evar_map * typeclass_error) CErrors.tag

val typeclass_error : env -> Evd.evar_map -> typeclass_error -> 'a

val not_a_class : env -> Evd.evar_map -> constr -> 'a

val unbound_method : env -> Evd.evar_map -> GlobRef.t -> lident -> 'a

val explain_typeclass_error
  : (env -> Evd.evar_map -> EConstr.constr -> Pp.t)
  -> env -> Evd.evar_map -> typeclass_error -> Pp.t
