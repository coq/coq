(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val warn_image : unit -> GMisc.image
val warning : string -> unit

val cb : GData.clipboard

val browse : (string -> unit) -> string -> unit
val browse_keyword : (string -> unit) -> string -> unit

val byte_offset_to_char_offset : string -> int -> int
val byte_off_to_buffer_off : GText.buffer -> int -> int
val buffer_off_to_byte_off : GText.buffer -> int -> int
val get_iter_at_byte : GText.buffer -> line:int -> int -> GText.iter

val ulen : int -> int

type timer = { run : ms:int -> callback:(unit->bool) -> unit;
               kill : unit -> unit }
val mktimer : unit -> timer

val do_convert : string -> string
val find_tag_limits : GText.tag -> GText.iter -> GText.iter * GText.iter
val find_tag_start : GText.tag -> GText.iter -> GText.iter
val find_tag_stop : GText.tag -> GText.iter -> GText.iter

val select_file_for_open :
  title:string -> ?filter:bool -> ?multiple:bool -> ?parent:GWindow.window -> ?filename:string -> unit -> string list
val select_file_for_save :
  title:string -> ?parent:GWindow.window -> ?filename:string -> unit -> string option
val try_convert : string -> string
val try_export : string -> string -> bool
val stock_to_widget :
  ?size:[`CUSTOM of int * int | Gtk.Tags.icon_size] ->
    GtkStock.id -> GObj.widget

val custom_rocqtop : string option ref
(* @return command to call rocqtop
   - custom_rocqtop if set
   - from the prefs is set
   - try to infer it else *)
val rocqtop_path : unit -> string


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

(** [encode_string_list l] encodes a list of strings into a single
    string using a "shell"-like encoding: it quotes strings
    containing space by surrounding them with single quotes, and,
    outside quoted strings, quotes both single quote and backslash
    by prefixing them with backslash; the encoding tries to be
    minimalistic. *)

val encode_string_list : string list -> string

(** [decode_string_list l] decodes the encoding of a string list as
    a string; it fails with a Failure if a single quote is unmatched
    or if a backslash in unquoted part is not followed by a single
    quote or another backslash. *)

val decode_string_list : string -> string list

(** filter key event to keep only the interesting modifiers *)

val filter_key : GdkEvent.Key.t -> Gdk.keysym * Gdk.Tags.modifier list
