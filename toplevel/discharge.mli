
(* $Id$ *)

(* This module implements the discharge mechanism. It provides a function to
   close the last opened section. That function calls [Lib.close_section] and
   then re-introduce all the discharged versions of the objects that were
   defined in the section. *)

val close_section : bool -> string -> unit

val save_module_to : string -> string -> unit
