
(* $Id$ *)

(*i*)
open Names
(*i*)

(* This module contains the table for globalization, which associates global
   names (section paths) to identifiers. *)

val push : identifier -> section_path -> unit

val sp_of_id : path_kind -> identifier -> section_path
val fw_sp_of_id : identifier -> section_path
