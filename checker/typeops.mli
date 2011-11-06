(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: typeops.mli 9427 2006-12-11 18:46:35Z bgregoir $ i*)

(*i*)
open Names
open Term
open Declarations
open Environ
(*i*)

(*s Typing functions (not yet tagged as safe) *)

val infer      : env -> constr      -> constr
val infer_type : env -> constr      -> sorts
val check_ctxt : env -> rel_context -> env
val check_named_ctxt : env -> named_context -> env
val check_polymorphic_arity :
  env -> rel_context -> polymorphic_arity -> unit

val type_of_constant_type : env -> constant_type -> constr

