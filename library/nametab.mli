
(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
(*i*)

(* This module contains the table for globalization, which associates global
   names (section paths) to identifiers. *)

type cci_table = global_reference Stringmap.t
type obj_table = (section_path * Libobject.obj) Stringmap.t
type mod_table = (section_path * module_contents) Stringmap.t
and module_contents = Closed of cci_table * obj_table * mod_table

val push : section_path -> global_reference -> unit
val push_object : section_path -> Libobject.obj -> unit
val push_module : section_path -> module_contents -> unit

val push_local : section_path -> global_reference -> unit
val push_local_object : section_path -> Libobject.obj -> unit

(* This should eventually disappear *)
val sp_of_id : path_kind -> identifier -> global_reference

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

(*s Roots of the space of absolute names *)

(* This is the root of the standard library of Coq *)
val coq_root : string

(* This is the default root for developments which doesn't mention a root *)
val default_root : string

(* This is to declare a new root *)
val push_library_root : string -> unit

