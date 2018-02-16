(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open EConstr
open Environ
open Constrexpr
(*i*)

type contexts = Parameters | Properties

type typeclass_error =
    | NotAClass of constr
    | UnboundMethod of Names.global_reference * Id.t Loc.located (* Class name, method *)
    | MismatchedContextInstance of contexts * constr_expr list * Context.Rel.t (* found, expected *)

exception TypeClassError of env * typeclass_error

let typeclass_error env err = raise (TypeClassError (env, err))

let not_a_class env c = typeclass_error env (NotAClass c)

let unbound_method env cid id = typeclass_error env (UnboundMethod (cid, id))

let mismatched_ctx_inst env c n m = typeclass_error env (MismatchedContextInstance (c, n, m))
