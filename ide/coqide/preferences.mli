(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val lang_manager : GSourceView3.source_language_manager
val style_manager : GSourceView3.source_style_scheme_manager

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

class virtual ['a] repr :
object
  method raw_into : string -> 'a
  method raw_from : 'a -> string
  method virtual into : string list -> 'a option
  method virtual from : 'a -> string list
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
  method repr: 'a repr
end

val list_tags : unit -> tag preference Util.String.Map.t

val get_unicode_bindings_local_file : unit -> string option
val get_unicode_bindings_default_file : unit -> string option

val str_to_mod_list : string -> Gdk.Tags.modifier list
val mod_list_to_str : Gdk.Tags.modifier list -> string

val printopts_item_names : string list ref

val select_arch : 'a -> 'a -> 'a

val cmd_rocqtop : string option preference
val cmd_rocqc : string preference
val cmd_make : string preference
val cmd_rocqmakefile : string preference
val cmd_rocqdoc : string preference
val source_language : string preference
val source_style : string preference
val global_auto_reload : bool preference
val global_auto_reload_delay : int preference
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
val modifier_for_display : string preference
val modifier_for_queries : string preference
val modifiers_valid : string preference
val cmd_browse : string preference
val cmd_editor : string preference
val text_font : string preference
val show_toolbar : bool preference
val window_width : int preference
val window_height : int preference
val unicode_binding : bool preference
val auto_complete : bool preference
val auto_complete_delay : int preference
val stop_before : bool preference
val reset_on_tab_switch : bool preference
val line_ending : line_ending preference
val document_tabs_pos : string preference
(* val background_color : string preference *)
val processing_color : string preference
val processed_color : string preference
val incompletely_processed_color : string preference
val unjustified_conclusion_color : string preference
val breakpoint_color : string preference
val db_stopping_point_color : string preference
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
val microPG : bool preference
val user_queries : (string * string) list preference
val diffs : string preference

val save_pref : unit -> unit
val load_pref : warn:(delay:int -> string -> unit) -> unit

val stick : 'a preference ->
  < connect : #GObj.widget_signals ; .. > -> ('a -> unit) -> unit

val use_default_doc_url : string
