
(*i $Id$ i*)

(*i*)
open Names
open Term
open Classops
open Declare
(*i*)

(* Classes and coercions. *)

val try_add_new_coercion : identifier -> strength -> unit
val try_add_new_coercion_subclass : identifier -> strength -> unit
val try_add_new_coercion_record : identifier -> strength -> identifier -> unit
val try_add_new_coercion_with_target : identifier -> strength ->
  identifier -> identifier -> bool -> unit

val try_add_new_class : identifier -> strength -> unit
val process_class :
  dir_path -> identifier list -> 
    (cl_typ * cl_info_typ) -> (cl_typ * cl_info_typ)
val process_coercion :
  dir_path -> (coe_typ * coe_info_typ) * cl_typ * cl_typ -> 
    (coe_typ * coe_info_typ) * cl_typ * cl_typ
