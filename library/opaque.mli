(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ *)

(*i*)
open Names
open Closure
open Safe_typing
open Environ
(*i*)

(* The current set of transparent constants and variables *)
val state : unit -> transparent_state

(* returns true if the global reference has a definition and that is
   has not been set opaque *)
val is_evaluable : env -> evaluable_global_reference -> bool

(* Modifying this state *)
val set_opaque_const : section_path -> unit
val set_transparent_const : section_path -> unit

val set_opaque_var : identifier -> unit
val set_transparent_var : identifier -> unit
