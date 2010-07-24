(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val async : ('a -> unit) -> 'a -> unit
val sync  : ('a -> 'b) -> 'a -> 'b

(* avoid running two instances of a function concurrently *)
val mutex : string -> ('a -> unit) -> 'a -> unit

val doc_url : unit -> string
val browse : (string -> unit) -> string -> unit
val browse_keyword : (string -> unit) -> string -> unit
val byte_offset_to_char_offset : string -> int -> int
val debug : bool ref
val disconnect_revert_timer : unit -> unit
val disconnect_auto_save_timer : unit -> unit
val do_convert : string -> string
val find_tag_limits : GText.tag -> GText.iter -> GText.iter * GText.iter
val find_tag_start : GText.tag -> GText.iter -> GText.iter
val find_tag_stop : GText.tag -> GText.iter -> GText.iter
val get_insert : < get_iter_at_mark : [> `INSERT] -> 'a; .. > -> 'a

val is_char_start : char -> bool

val lib_ide_file : string -> string
val my_stat : string -> Unix.stats option

val prerr_endline : string -> unit
val prerr_string : string -> unit
val print_id : 'a -> unit

val revert_timer : GMain.Timeout.id option ref
val auto_save_timer : GMain.Timeout.id option ref
val select_file_for_open :
  title:string ->
  ?dir:string ref -> ?filename:string -> unit -> string option
val select_file_for_save :
  title:string ->
  ?dir:string ref -> ?filename:string -> unit -> string option
val set_highlight_timer : (unit -> 'a) -> unit
val try_convert : string -> string
val try_export : string -> string -> bool
val stock_to_widget :  ?size:Gtk.Tags.icon_size -> GtkStock.id -> GObj.widget

open Format
val print_list : (formatter -> 'a -> unit) -> formatter -> 'a list -> unit

val run_command : (string -> unit) -> string -> Unix.process_status*string



val status : GMisc.statusbar
val push_info : string -> unit
val pop_info : unit -> unit
val flash_info : ?delay:int -> string -> unit

val set_location : (string -> unit) ref

val pbar : GRange.progress_bar


(*
  checks if two file names refer to the same (existing) file
*)

val same_file : string -> string -> bool

(*
  returns an absolute filename equivalent to given filename
*)
val absolute_filename : string -> string
