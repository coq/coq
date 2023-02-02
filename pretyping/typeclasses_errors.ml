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
    | UnboundMethod of GlobRef.t * lident (* Class name, method *)

type _ CErrors.tag += TypeClassError : (env * Evd.evar_map * typeclass_error) CErrors.tag

let typeclass_error env sigma err = CErrors.coq_error TypeClassError (env, sigma, err)

let not_a_class env sigma c = typeclass_error env sigma (NotATypeclass c)

let unbound_method env sigma cid id = typeclass_error env sigma (UnboundMethod (cid, id))

open Pp

let explain_not_a_class prc env sigma c =
  prc env sigma c ++ str" is not a declared type class."

let explain_unbound_method env sigma cid { CAst.v = id } =
  str "Unbound method name " ++ Id.print (id) ++ spc () ++
  str"of class" ++ spc () ++ Nametab.pr_global_env Id.Set.empty cid ++ str "."

let explain_typeclass_error prc env sigma = function
  | NotATypeclass c -> explain_not_a_class prc env sigma c
  | UnboundMethod (cid, id) -> explain_unbound_method env sigma cid id
