(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.ml 6748 2005-02-18 22:17:50Z herbelin $ i*)

(*i*)
open Names
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Topconstr
open Util
(*i*)

type contexts = Parameters | Properties

type typeclass_error = 
    | UnboundClass of identifier located
    | NoInstance of identifier located * constr list
    | MismatchedContextInstance of contexts * constr_expr list * named_context (* found, expected *)

exception TypeClassError of env * typeclass_error

let typeclass_error env err = raise (TypeClassError (env, err))

let unbound_class env id = typeclass_error env (UnboundClass id)

let no_instance env id args = typeclass_error env (NoInstance (id, args))

let mismatched_ctx_inst env c n m = typeclass_error env (MismatchedContextInstance (c, n, m))
