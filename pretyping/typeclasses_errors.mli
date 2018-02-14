(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Environ
open Constrexpr
open Globnames

type contexts = Parameters | Properties

type typeclass_error =
  | NotAClass of constr
  | UnboundMethod of global_reference * Misctypes.lident (** Class name, method *)
  | MismatchedContextInstance of contexts * constr_expr list * Context.Rel.t (** found, expected *)

exception TypeClassError of env * typeclass_error

val not_a_class : env -> constr -> 'a

val unbound_method : env -> global_reference -> Misctypes.lident -> 'a

val mismatched_ctx_inst : env -> contexts -> constr_expr list -> Context.Rel.t -> 'a

