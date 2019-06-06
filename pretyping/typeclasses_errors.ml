(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
    | UnboundMethod of GlobRef.t * lident (* Class name, method *)

exception TypeClassError of env * Evd.evar_map * typeclass_error

let typeclass_error env sigma err = raise (TypeClassError (env, sigma, err))

let not_a_class env sigma c = typeclass_error env sigma (NotAClass c)

let unbound_method env sigma cid id = typeclass_error env sigma (UnboundMethod (cid, id))
