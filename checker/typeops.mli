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
open Cic
open Environ
(*i*)

(*s Typing functions (not yet tagged as safe) *)

val infer      : env -> constr      -> constr
val infer_type : env -> constr      -> sorts
val check_ctxt : env -> rel_context -> env
val check_polymorphic_arity :
  env -> rel_context -> template_arity -> unit
