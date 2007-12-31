(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.mli 6748 2005-02-18 22:17:50Z herbelin $ i*)

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
    | UnboundMethod of identifier * identifier located (* Class name, method *)
    | NoInstance of identifier located * constr list
    | MismatchedContextInstance of contexts * constr_expr list * named_context (* found, expected *)

exception TypeClassError of env * typeclass_error

val unbound_class : env -> identifier located -> 'a

val unbound_method : env -> identifier -> identifier located -> 'a

val no_instance : env -> identifier located -> constr list -> 'a

val mismatched_ctx_inst : env -> contexts -> constr_expr list -> named_context -> 'a
