(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

val async : ('a -> unit) -> 'a -> unit
val browse : string -> unit
val browse_keyword : string -> unit
val byte_offset_to_char_offset : string -> int -> int
val clear_stdout : unit -> unit
val debug : bool ref
val disconnect_revert_timer : unit -> unit
val disconnect_auto_save_timer : unit -> unit
val do_convert : string -> string
val find_tag_limits : GText.tag -> GText.iter -> GText.iter * GText.iter
val find_tag_start : GText.tag -> GText.iter -> GText.iter
val find_tag_stop : GText.tag -> GText.iter -> GText.iter
val get_insert : < get_iter_at_mark : [> `INSERT] -> 'a; .. > -> 'a

val is_char_start : char -> bool

val lib_ide : string
val my_stat : string -> Unix.stats option

val prerr_endline : string -> unit
val prerr_string : string -> unit
val print_id : 'a -> unit

val process_pending : unit -> unit
val read_stdout : unit -> string
val revert_timer : GMain.Timeout.id option ref
val auto_save_timer : GMain.Timeout.id option ref
val select_file :
  title:string ->
  ?dir:string ref -> ?filename:string -> unit -> string option
val set_highlight_timer : (unit -> 'a) -> unit
val try_convert : string -> string
val try_export : string -> string -> bool
val stock_to_widget :  ?size:Gtk.Tags.icon_size -> GtkStock.id -> GObj.widget

open Format
val print_list : (formatter -> 'a -> unit) -> formatter -> 'a list -> unit

val run_command : (string -> unit) -> string -> Unix.process_status*string


val prime : Glib.unichar
val underscore : Glib.unichar
val arobase : Glib.unichar
val bn : Glib.unichar
val space : Glib.unichar
val tab : Glib.unichar


val status : GMisc.statusbar option ref 
val push_info : (string -> unit) ref
val pop_info : (unit -> unit) ref
val flash_info : (?delay:int -> string -> unit) ref

val set_location : (string -> unit) ref

val pulse : (unit -> unit) ref
