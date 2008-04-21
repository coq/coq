(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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

val type_of_constant_type : env -> constant_type -> constr

