(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Pp
open Identifier
open Names
open Term
open Libnames
(*i*)

(*s This module contains the table for globalization, which associates global
   names (section paths) to qualified names. *)

type extended_global_reference =
  | TrueGlobal of global_reference
  | SyntacticDef of section_path

exception GlobalizationError of qualid

(* Raises a globalization error *)
val error_global_not_found_loc : loc -> qualid -> 'a
val error_global_not_found     : qualid -> 'a

(*s Register visibility of absolute paths by qualified names *)
val push : section_path -> global_reference -> unit
val push_syntactic_definition : section_path -> unit

(*s Register visibility of absolute paths by short names *)
val push_short_name : identifier -> global_reference -> unit
val push_short_name_syntactic_definition : section_path -> unit
val push_short_name_object : section_path -> unit

(*s Register visibility by all qualifications *)
val push_section : dir_path -> unit

(*s The following functions perform globalization of qualified names *)

val locate : qualid -> global_reference

(* This locates also syntactic definitions *)
val extended_locate : qualid -> extended_global_reference

val locate_obj : qualid -> section_path

val locate_constant : qualid -> constant_path
val locate_mind : qualid -> mutual_inductive_path
val locate_section : qualid -> dir_path
val locate_module : qualid -> module_path

(* [exists sp] tells if [sp] is already bound to a cci term *)
val exists_cci : section_path -> bool
val exists_section : dir_path -> bool
val exists_module : dir_path -> bool

(* lookup the other way around, gives names of constructors and
inductive types. May raise Not_found *)

val get_sp : global_reference -> section_path
val get_full_qualid : global_reference -> qualid
val get_short_qualid : global_reference -> qualid
val get_ident : global_reference -> identifier

(*
val open_module_contents : qualid -> unit
val rec_open_module_contents : qualid -> unit

(*s Entry points for sections *)
val open_section_contents : qualid -> unit
val push_section : section_path -> module_contents -> unit
*)
(*s Roots of the space of absolute names *)

(* This is the root of the standard library of Coq *)
val coq_root : module_ident

(* This is the default root prefix for developments which doesn't mention a root *)
val default_root_prefix : dir_path

(* This is to declare a new root *)
val push_library_root : module_ident -> unit

(* This turns a "user" absolute name into a global reference;
   especially, constructor/inductive names are turned into internal
   references inside a block of mutual inductive *)
val absolute_reference : section_path -> global_reference

val is_absolute_dirpath : dir_path -> bool

(* [locate_in_absolute_module dir id] finds [id] in module [dir] or in
   one of its section/subsection *)
val locate_in_absolute_module : dir_path -> identifier -> global_reference

val push_loaded_library : dir_path -> unit
val locate_loaded_library : qualid -> dir_path



type frozen

val freeze : unit -> frozen
val unfreeze : frozen -> unit
