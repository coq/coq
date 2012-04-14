(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type project_behavior = Ignore_args | Append_args | Subst_args
type inputenc = Elocale | Eutf8 | Emanual of string

type pref =
    {
      mutable cmd_coqc : string;
      mutable cmd_make : string;
      mutable cmd_coqmakefile : string;
      mutable cmd_coqdoc : string;

      mutable global_auto_revert : bool;
      mutable global_auto_revert_delay : int;

      mutable auto_save : bool;
      mutable auto_save_delay : int;
      mutable auto_save_name : string * string;

      mutable read_project : project_behavior;
      mutable project_file_name : string;

      mutable encoding : inputenc;

      mutable automatic_tactics : string list;
      mutable cmd_print : string;

      mutable modifier_for_navigation : string;
      mutable modifier_for_templates : string;
      mutable modifier_for_tactics : string;
      mutable modifier_for_display : string;
      mutable modifiers_valid : string;

      mutable cmd_browse : string;
      mutable cmd_editor : string;

      mutable text_font : Pango.font_description;

      mutable doc_url : string;
      mutable library_url : string;

      mutable show_toolbar : bool;
      mutable contextual_menus_on_goal : bool;
      mutable window_width : int;
      mutable window_height : int;
      mutable query_window_width : int;
      mutable query_window_height : int;
(*
      mutable use_utf8_notation : bool;
*)
      mutable auto_complete : bool;
      mutable stop_before : bool;
      mutable lax_syntax : bool;
      mutable vertical_tabs : bool;
      mutable opposite_tabs : bool;

      mutable background_color : string;
      mutable processing_color : string;
      mutable processed_color : string;
    }

val save_pref : unit -> unit
val load_pref : unit -> unit

val current : pref ref

val configure : ?apply:(unit -> unit) -> unit -> unit

val change_font : (Pango.font_description -> unit) ref
val change_background_color : (Gdk.color -> unit) ref
val show_toolbar : (bool -> unit) ref
val auto_complete : (bool -> unit) ref
val resize_window : (unit -> unit) ref

val use_default_doc_url : string
