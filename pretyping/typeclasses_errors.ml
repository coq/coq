(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open EConstr
open Environ
open Constrexpr
open Globnames
(*i*)

type contexts = Parameters | Properties

type typeclass_error =
    | NotAClass of constr
    | UnboundMethod of global_reference * Misctypes.lident (* Class name, method *)
    | MismatchedContextInstance of contexts * constr_expr list * Context.Rel.t (* found, expected *)

exception TypeClassError of env * typeclass_error

let typeclass_error env err = raise (TypeClassError (env, err))

let not_a_class env c = typeclass_error env (NotAClass c)

let unbound_method env cid id = typeclass_error env (UnboundMethod (cid, id))

let mismatched_ctx_inst env c n m = typeclass_error env (MismatchedContextInstance (c, n, m))
