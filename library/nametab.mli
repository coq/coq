
(* $Id$ *)

(*i*)
open Util
open Names
open Term
(*i*)

(* This module contains the table for globalization, which associates global
   names (section paths) to identifiers. *)

type cci_table = global_reference Stringmap.t
type obj_table = (section_path * Libobject.obj) Stringmap.t
type mod_table = module_contents Stringmap.t
and module_contents = Closed of cci_table * obj_table * mod_table

val push : identifier -> global_reference -> unit
val push_object : identifier -> (section_path * Libobject.obj) -> unit
val push_module : string -> module_contents -> unit

val sp_of_id : path_kind -> identifier -> global_reference

(* This returns the section path of a constant or fails with [Not_found] *)
val constant_sp_of_id : identifier -> section_path

val locate : qualid -> global_reference
val locate_obj : qualid -> (section_path * Libobject.obj)
val locate_constant : qualid -> constant_path

val open_module_contents : string -> unit
val rec_open_module_contents : string -> unit



