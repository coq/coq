(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Declarations
open Entries
open Libnames
(*i*)

(* This modules provides official fucntions to declare modules and
   module types *)

(* experimental for now *)
(*
val declare_module : label -> module_entry -> unit

val begin_module : 
  label -> identifier list -> (mod_bound_id * module_type_entry) list 
    -> module_type_entry option -> unit
val end_module : label -> unit

val begin_modtype : 
  label -> identifier list -> (mod_bound_id * module_type_entry) list 
    -> unit
val end_modtype : label -> unit
*)
(* [push_module_components dir mp short] adds components to Nametab
   if short=true adds short names as well *)

val push_module_with_components : 
  dir_path -> module_path -> bool -> unit
(*
val debug_print_modtab : unit -> Pp.std_ppcmds
*)
(*val debug_print_modtypetab : unit -> Pp.std_ppcmds*)
