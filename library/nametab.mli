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

(* Raises a globalization error *)
val error_global_not_found_loc : loc -> qualid -> 'a

(*s Names tables *)
type cci_table = global_reference Idmap.t
type obj_table = (section_path * Libobject.obj) Idmap.t
type mod_table = (section_path * module_contents) Stringmap.t
and module_contents = Closed of cci_table * obj_table * mod_table

(*s Registers absolute paths *)
val push : section_path -> global_reference -> unit
val push_object : section_path -> Libobject.obj -> unit
val push_module : section_path -> module_contents -> unit

val push_local : section_path -> global_reference -> unit
val push_local_object : section_path -> Libobject.obj -> unit

(* This should eventually disappear *)
val sp_of_id : path_kind -> identifier -> global_reference

(*s The following functions perform globalization of qualified names *)

(* This returns the section path of a constant or fails with [Not_found] *)
val constant_sp_of_id : identifier -> section_path

val locate : qualid -> global_reference
val locate_obj : qualid -> (section_path * Libobject.obj)
val locate_constant : qualid -> constant_path
val locate_module : qualid -> section_path * module_contents

(* [exists sp] tells if [sp] is already bound to a cci term *)
val exists_cci : section_path -> bool
val exists_module : section_path -> bool

val open_module_contents : qualid -> unit
val rec_open_module_contents : qualid -> unit

(*s Entry points for sections *)
val open_section_contents : qualid -> unit
val push_section : section_path -> module_contents -> unit

(*s Roots of the space of absolute names *)

(* This is the root of the standard library of Coq *)
val coq_root : string

(* This is the default root for developments which doesn't mention a root *)
val default_root : string

(* This is to declare a new root *)
val push_library_root : string -> unit

(* This turns a "user" absolute name into a global reference;
   especially, constructor/inductive names are turned into internal
   references inside a block of mutual inductive *)
val absolute_reference : section_path -> global_reference

(* [locate_in_absolute_module dir id] finds [id] in module [dir] or in
   one of its section/subsection *)
val locate_in_absolute_module : dir_path -> identifier -> global_reference
