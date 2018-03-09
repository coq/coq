(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val warn_image : unit -> GMisc.image
val warning : string -> unit

val cb : GData.clipboard

val doc_url : unit -> string
val browse : (string -> unit) -> string -> unit
val browse_keyword : (string -> unit) -> string -> unit

(* These two functions are equivalent, the latter is named following
   glib schema, and exists in glib but is not in lablgtk2 *)
val byte_offset_to_char_offset : string -> int -> int
val glib_utf8_pos_to_offset : string -> off:int -> int

type timer = { run : ms:int -> callback:(unit->bool) -> unit;
               kill : unit -> unit }
val mktimer : unit -> timer

val do_convert : string -> string
val find_tag_limits : GText.tag -> GText.iter -> GText.iter * GText.iter
val find_tag_start : GText.tag -> GText.iter -> GText.iter
val find_tag_stop : GText.tag -> GText.iter -> GText.iter

val select_file_for_open : title:string -> ?filename:string -> unit -> string option
val select_file_for_save :
  title:string -> ?filename:string -> unit -> string option
val try_convert : string -> string
val try_export : string -> string -> bool
val stock_to_widget :
  ?size:[`CUSTOM of int * int | Gtk.Tags.icon_size] ->
    GtkStock.id -> GObj.widget

val custom_coqtop : string option ref
(* @return command to call coqtop
   - custom_coqtop if set
   - from the prefs is set
   - try to infer it else *)
val coqtop_path : unit -> string


val status : GMisc.statusbar
val push_info : string -> unit
val pop_info : unit -> unit
val clear_info : unit -> unit
val flash_info : ?delay:int -> string -> unit

val insert_xml : ?mark:GText.mark -> ?tags:GText.tag list ->
  #GText.buffer_skel -> Richpp.richpp -> unit

val set_location : (string -> unit) ref
val display_location : GText.iter -> unit

(* In win32, when a command-line is to be executed via cmd.exe
   (i.e. Sys.command, Unix.open_process, ...), it cannot contain several
   quoted "..." zones otherwise some quotes are lost. Solution: we re-quote
   everything. Reference: http://ss64.com/nt/cmd.html *)

val requote : string -> string

val textview_width : #GText.view_skel -> int
(** Returns an approximate value of the character width of a textview *)

type logger = Feedback.level -> Pp.t -> unit

val default_logger : logger
(** Default logger. It logs messages that the casual user should not see. *)

(** {6 I/O operations} *)

(** A customized [stat] function. Exceptions are caught. *)

type stats = MTime of float | NoSuchFile | OtherError
val stat : string -> stats

(** Read the content of file [f] and add it to buffer [b].
    I/O Exceptions are propagated. *)

val read_file : string -> Buffer.t -> unit

(** Read what is available on a gtk input channel.
    This channel should have been set as non-blocking. *)

val io_read_all : Glib.Io.channel -> string

(** [run_command display finally cmd] allow to run a command
    asynchronously, calling [display] on any output of this command
    and [finally] when the command has returned. *)

val run_command :
  (string -> unit) -> (Unix.process_status -> unit) -> string -> unit

(* Checks if an error message is printable, it not replaces it with
 * a printable error *)
val validate : Pp.t -> Pp.t
