(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Some utility functions to be reused in module [Haskell]. *)

open Pp
open Miniml
open Names
open Term

val string : string -> std_ppcmds
val open_par : bool -> std_ppcmds
val close_par : bool -> std_ppcmds

val collect_lambda : ml_ast -> identifier list * ml_ast
val push_vars : identifier list -> identifier list * Idset.t ->
  identifier list * (identifier list * Idset.t)

val current_module : identifier option ref

val module_of_r : global_reference -> module_ident

val string_of_r : global_reference -> string

val check_ml : global_reference -> string -> string

val module_option : global_reference -> string

(*s Production of Ocaml syntax. We export both a functor to be used for 
    extraction in the Coq toplevel and a function to extract some 
    declarations to a file. *)

open Mlutil

module Make : functor(P : Mlpp_param) -> Mlpp

val current_module : Names.identifier option ref
val extract_to_file : 
  string -> extraction_params -> ml_decl list -> unit


