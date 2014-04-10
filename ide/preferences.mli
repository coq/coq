(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val lang_manager : GSourceView2.source_language_manager
val style_manager : GSourceView2.source_style_scheme_manager

type project_behavior = Ignore_args | Append_args | Subst_args
type inputenc = Elocale | Eutf8 | Emanual of string

type pref =
    {
      mutable cmd_coqtop : string option;
      mutable cmd_coqc : string;
      mutable cmd_make : string;
      mutable cmd_coqmakefile : string;
      mutable cmd_coqdoc : string;

      mutable source_language : string;
      mutable source_style : string;

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
      mutable reset_on_tab_switch : bool;
      mutable vertical_tabs : bool;
      mutable opposite_tabs : bool;

      mutable background_color : string;
      mutable processing_color : string;
      mutable processed_color : string;
      mutable error_color : string;

      mutable dynamic_word_wrap : bool;
      mutable show_line_number : bool;
      mutable auto_indent : bool;
      mutable show_spaces : bool;
      mutable show_right_margin : bool;
      mutable spaces_instead_of_tabs : bool;
      mutable tab_length : int;
      mutable highlight_current_line : bool;

      mutable nanoPG : bool;

    }

val save_pref : unit -> unit
val load_pref : unit -> unit

val current : pref

val configure : ?apply:(unit -> unit) -> unit -> unit

(* Hooks *)
val refresh_editor_hook : (unit -> unit) ref
val refresh_style_hook : (unit -> unit) ref
val refresh_language_hook : (unit -> unit) ref
val refresh_toolbar_hook : (unit -> unit) ref
val resize_window_hook : (unit -> unit) ref
val refresh_tabs_hook : (unit -> unit) ref

val use_default_doc_url : string
