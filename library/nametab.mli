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
(*i*)

(*s This module contains the table for globalization, which associates global
   names (section paths) to qualified names. *)

type global_reference =
  | VarRef of variable
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

(* Finds the real name of a global (e.g. fetch the constructor names
   from the inductive name and constructor number) *)
val sp_of_global : Environ.env -> global_reference -> section_path

type extended_global_reference =
  | TrueGlobal of global_reference
  | SyntacticDef of section_path

(*s A [qualid] is a partially qualified ident; it includes fully
    qualified names (= absolute names) and all intermediate partial
    qualifications of absolute names, including single identifiers *)
type qualid

val make_qualid : dir_path -> identifier -> qualid
val repr_qualid : qualid -> dir_path * identifier
val make_short_qualid : identifier -> qualid

val string_of_qualid : qualid -> string
val pr_qualid : qualid -> std_ppcmds

val qualid_of_sp : section_path -> qualid

(* Turns an absolute name into a qualified name denoting the same name *)
val shortest_qualid_of_global : Environ.env -> global_reference -> qualid

(* Printing of global references using names as short as possible *)
val pr_global_env : Environ.env -> global_reference -> std_ppcmds

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
val push_short_name_syntactic_definition : section_path -> unit
val push_short_name_object : section_path -> unit

(*s Register visibility of absolute paths by short names *)
val push_tactic_path : section_path -> unit
val locate_tactic : qualid -> section_path

(*s Register visibility by all qualifications *)
val push_section : dir_path -> unit

(* This should eventually disappear *)
val sp_of_id : identifier -> global_reference

(*s The following functions perform globalization of qualified names *)

(* This returns the section path of a constant or fails with [Not_found] *)
val constant_sp_of_id : identifier -> section_path

val locate : qualid -> global_reference

(* This function is used to transform a qualified identifier into a
   global reference, with a nice error message in case of failure *)
val global : qualid located -> global_reference

(* The same for inductive types *)
val global_inductive : qualid located -> inductive

(* This locates also syntactic definitions *)
val extended_locate : qualid -> extended_global_reference

val locate_obj : qualid -> section_path

val locate_constant : qualid -> constant
val locate_section : qualid -> dir_path

(* [exists sp] tells if [sp] is already bound to a cci term *)
val exists_cci : section_path -> bool
val exists_section : dir_path -> bool

(*s Roots of the space of absolute names *)

(* This turns a "user" absolute name into a global reference;
   especially, constructor/inductive names are turned into internal
   references inside a block of mutual inductive *)
val absolute_reference : section_path -> global_reference

(* [locate_in_absolute_module dir id] finds [id] in module [dir] or in
   one of its section/subsection *)
val locate_in_absolute_module : dir_path -> identifier -> global_reference

val push_loaded_library : dir_path -> unit
val locate_loaded_library : qualid -> dir_path
