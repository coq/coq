
(* $Id$ *)

(*i*)
open Names
open Term
open Classops
open Declare
(*i*)

(* Classes and coercions. *)

val try_add_new_coercion : identifier -> strength -> unit
val try_add_new_coercion_subclass : identifier -> strength -> unit
val try_add_new_coercion_record: identifier -> strength -> section_path -> unit
val try_add_new_coercion_with_target : identifier -> strength ->
  identifier -> identifier -> bool -> unit

val try_add_new_class : identifier -> strength -> unit
val process_class :
  section_path -> (cl_typ * cl_info_typ) -> (cl_typ * cl_info_typ)
val process_coercion :
  section_path -> (coe_typ * coe_info_typ) * cl_typ * cl_typ -> 
    ((coe_typ * coe_info_typ) * cl_typ * cl_typ) * identifier * int 

val defined_in_sec : section_path -> section_path -> bool
val coercion_syntax : identifier -> int -> cl_typ -> unit
val fun_coercion_syntax_entry : identifier -> int -> unit
val coercion_syntax_entry : identifier -> int -> unit
