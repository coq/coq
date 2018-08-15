(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val lang_manager : GSourceView2.source_language_manager
val style_manager : GSourceView2.source_style_scheme_manager

type project_behavior = Ignore_args | Append_args | Subst_args
type inputenc = Elocale | Eutf8 | Emanual of string
type line_ending = [ `DEFAULT | `WINDOWS | `UNIX ]

type tag = {
  tag_fg_color : string option;
  tag_bg_color : string option;
  tag_bold : bool;
  tag_italic : bool;
  tag_underline : bool;
  tag_strikethrough : bool;
}

class type ['a] repr =
object
  method into : string list -> 'a option
  method from : 'a -> string list
end

class ['a] preference_signals : changed:'a GUtil.signal ->
object
  inherit GUtil.ml_signals
  method changed : callback:('a -> unit) -> GtkSignal.id
end

class ['a] preference : name:string list -> init:'a -> repr:'a repr ->
object
  method connect : 'a preference_signals
  method get : 'a
  method set : 'a -> unit
  method reset : unit -> unit
  method default : 'a
end

val list_tags : unit -> tag preference Util.String.Map.t

val cmd_coqtop : string option preference
val cmd_coqc : string preference
val cmd_make : string preference
val cmd_coqmakefile : string preference
val cmd_coqdoc : string preference
val source_language : string preference
val source_style : string preference
val global_auto_revert : bool preference
val global_auto_revert_delay : int preference
val auto_save : bool preference
val auto_save_delay : int preference
val auto_save_name : (string * string) preference
val read_project : project_behavior preference
val project_file_name : string preference
val project_path : string option preference
val encoding : inputenc preference
val automatic_tactics : string list preference
val cmd_print : string preference
val modifier_for_navigation : string preference
val modifier_for_templates : string preference
val modifier_for_tactics : string preference
val modifier_for_display : string preference
val modifier_for_queries : string preference
val modifiers_valid : string preference
val cmd_browse : string preference
val cmd_editor : string preference
val text_font : string preference
val doc_url : string preference
val library_url : string preference
val show_toolbar : bool preference
val contextual_menus_on_goal : bool preference
val window_width : int preference
val window_height : int preference
val auto_complete : bool preference
val stop_before : bool preference
val reset_on_tab_switch : bool preference
val line_ending : line_ending preference
val vertical_tabs : bool preference
val opposite_tabs : bool preference
val background_color : string preference
val processing_color : string preference
val processed_color : string preference
val error_color : string preference
val error_fg_color : string preference
val dynamic_word_wrap : bool preference
val show_line_number : bool preference
val auto_indent : bool preference
val show_spaces : bool preference
val show_right_margin : bool preference
val show_progress_bar : bool preference
val spaces_instead_of_tabs : bool preference
val tab_length : int preference
val highlight_current_line : bool preference
val nanoPG : bool preference
val user_queries : (string * string) list preference
val diffs : string preference

val save_pref : unit -> unit
val load_pref : unit -> unit

val configure : ?apply:(unit -> unit) -> unit -> unit

val stick : 'a preference ->
  (#GObj.widget as 'obj) -> ('a -> unit) -> unit

val use_default_doc_url : string
