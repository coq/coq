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
open Names
open Term
(*i*)

(*s This module contains the table for globalization, which associates global
   names (section paths) to qualified names. *)

type extended_global_reference =
  | TrueGlobal of global_reference
  | SyntacticDef of section_path

(*s A [qualid] is a partially qualified ident; it includes fully
    qualified names (= absolute names) and all intermediate partial
    qualifications of absolute names, including single identifiers *)
type qualid

val make_qualid : dir_path -> identifier -> qualid
val repr_qualid : qualid -> dir_path * identifier

val string_of_qualid : qualid -> string
val pr_qualid : qualid -> std_ppcmds

(* Turns an absolute name into a qualified name denoting the same name *)
val qualid_of_sp : section_path -> qualid

exception GlobalizationError of qualid
exception GlobalizationConstantError of qualid

(* Raises a globalization error *)
val error_global_not_found_loc : loc -> qualid -> 'a
val error_global_not_found     : qualid -> 'a
val error_global_constant_not_found_loc : loc -> qualid -> 'a

(*s Register visibility of absolute paths by qualified names *)
val push : visibility:int -> section_path -> global_reference -> unit
val push_syntactic_definition : section_path -> unit

(*s Register visibility of absolute paths by short names *)
(*
val push_short_name : section_path -> global_reference -> unit
*)
val push_short_name_syntactic_definition : section_path -> unit
val push_short_name_object : section_path -> unit

(*s Register visibility by all qualifications *)
val push_section : dir_path -> unit

(* This should eventually disappear *)
val sp_of_id : path_kind -> identifier -> global_reference

(*s The following functions perform globalization of qualified names *)

(* This returns the section path of a constant or fails with [Not_found] *)
val constant_sp_of_id : identifier -> section_path

val locate : qualid -> global_reference

(* This locates also syntactic definitions *)
val extended_locate : qualid -> extended_global_reference

val locate_obj : qualid -> section_path

val locate_constant : qualid -> constant_path
val locate_section : qualid -> dir_path

(* [exists sp] tells if [sp] is already bound to a cci term *)
val exists_cci : section_path -> bool
val exists_section : dir_path -> bool

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

(* [locate_in_absolute_module dir id] finds [id] in module [dir] or in
   one of its section/subsection *)
val locate_in_absolute_module : dir_path -> identifier -> global_reference

val push_loaded_library : dir_path -> unit
val locate_loaded_library : qualid -> dir_path
