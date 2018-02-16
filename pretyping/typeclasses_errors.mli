(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open EConstr
open Environ
open Constrexpr

type contexts = Parameters | Properties

type typeclass_error =
  | NotAClass of constr
  | UnboundMethod of global_reference * Id.t located (** Class name, method *)
  | MismatchedContextInstance of contexts * constr_expr list * Context.Rel.t (** found, expected *)

exception TypeClassError of env * typeclass_error

val not_a_class : env -> constr -> 'a

val unbound_method : env -> global_reference -> Id.t located -> 'a

val mismatched_ctx_inst : env -> contexts -> constr_expr list -> Context.Rel.t -> 'a

