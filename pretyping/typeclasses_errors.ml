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
open Libnames
(*i*)

type contexts = Parameters | Properties

type typeclass_error = 
    | NotAClass of constr
    | UnboundMethod of global_reference * identifier located (* Class name, method *)
    | NoInstance of identifier located * constr list
    | UnsatisfiableConstraints of evar_map
    | MismatchedContextInstance of contexts * constr_expr list * named_context (* found, expected *)

exception TypeClassError of env * typeclass_error

let typeclass_error env err = raise (TypeClassError (env, err))

let not_a_class env c = typeclass_error env (NotAClass c)

let unbound_method env cid id = typeclass_error env (UnboundMethod (cid, id))

let no_instance env id args = typeclass_error env (NoInstance (id, args))

let unsatisfiable_constraints env evm = typeclass_error env (UnsatisfiableConstraints evm)

let mismatched_ctx_inst env c n m = typeclass_error env (MismatchedContextInstance (c, n, m))
