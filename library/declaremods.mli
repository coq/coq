(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Identifier
open Names
open Mod_declarations
open Libnames
(*i*)

(* This modules provides official fucntions to declare modules and
   module types *)

(* experimental for now *)

val declare_module : label -> module_entry -> unit

val begin_module : 
  label -> identifier list -> (mod_bound_id * module_type_entry) list 
    -> module_type_entry option -> unit
val end_module : label -> unit


(*type module_disk = { 
  md_name : compilation_unit_name;
  md_compiled_env : compiled_module;
  md_declarations : library_segment;
  md_deps : (compilation_unit_name * Digest.t * bool) list }

val declare_disk_module : dir_path -> module_disk -> unit
*)

val begin_modtype : 
  label -> identifier list -> (mod_bound_id * module_type_entry) list 
    -> unit
val end_modtype : label -> unit

(* [push_module_components dir mp short] adds components to Nametab
   if short=true adds short names as well *)

val push_module_with_components : 
  section_path -> module_path -> bool -> unit



(*s Modules on disk contain the following informations (after the magic 
    number, and before dependencies and the digest). *)

type comp_unit_name = dir_path

type comp_unit = { 
  md_name : comp_unit_name;
  md_compiled_env : Safe_env.compiled_module;
  md_objects : mod_str_id * Lib.library_segment * Lib.library_segment}

val register_comp_unit : comp_unit -> Digest.t -> unit
val re_register_comp_unit : comp_unit_name -> unit


(*
It will be that nice after we put dependency traversal in the preparation phase 

type comp_unit_objects

val calculate_objects : comp_unit -> comp_unit_objects

(* the bool says if the module should be added to the environment as well *)

val register_comp_unit : 
  bool -> comp_unit -> comp_unit_objects -> Digest.t -> unit
*)


(* [import_module mp] opens the module [mp] (in a Caml sense). 
   It modifies Nametab and performs the "open_object" function 
   for every object of the module. *)

val import_module : module_path -> unit


val debug_print_modtab : unit -> Pp.std_ppcmds

(*val debug_print_modtypetab : unit -> Pp.std_ppcmds*)
