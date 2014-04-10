(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Configwin

let pref_file = Filename.concat (Minilib.coqide_config_home ()) "coqiderc"
let accel_file = Filename.concat (Minilib.coqide_config_home ()) "coqide.keys"
let lang_manager = GSourceView2.source_language_manager ~default:true
let () = lang_manager#set_search_path
  ((Minilib.coqide_data_dirs ())@lang_manager#search_path)
let style_manager = GSourceView2.source_style_scheme_manager ~default:true
let () = style_manager#set_search_path
  ((Minilib.coqide_data_dirs ())@style_manager#search_path)

let get_config_file name =
  let find_config dir = Sys.file_exists (Filename.concat dir name) in
  let config_dir = List.find find_config (Minilib.coqide_config_dirs ()) in
  Filename.concat config_dir name

(* Small hack to handle v8.3 to v8.4 change in configuration file *)
let loaded_pref_file =
  try get_config_file "coqiderc"
  with Not_found -> Filename.concat (Option.default "" (Glib.get_home_dir ())) ".coqiderc"

let loaded_accel_file =
  try get_config_file "coqide.keys"
  with Not_found -> Filename.concat (Option.default "" (Glib.get_home_dir ())) ".coqide.keys"

let mod_to_str m =
  match m with
    | `MOD1 -> "<Alt>"
    | `MOD2 -> "<Mod2>"
    | `MOD3 -> "<Mod3>"
    | `MOD4 -> "<Mod4>"
    | `MOD5 -> "<Mod5>"
    | `CONTROL -> "<Control>"
    | `SHIFT -> "<Shift>"
    | `HYPER -> "<Hyper>"
    | `META -> "<Meta>"
    | `RELEASE -> ""
    | `SUPER -> "<Super>"
    |  `BUTTON1| `BUTTON2| `BUTTON3| `BUTTON4| `BUTTON5| `LOCK -> ""

let mod_list_to_str l = List.fold_left (fun s m -> (mod_to_str m)^s) "" l

let str_to_mod_list s = snd (GtkData.AccelGroup.parse s)

type project_behavior = Ignore_args | Append_args | Subst_args

let string_of_project_behavior = function
  |Ignore_args -> "ignored"
  |Append_args -> "appended to arguments"
  |Subst_args -> "taken instead of arguments"

let project_behavior_of_string s =
  if s = "taken instead of arguments" then Subst_args
  else if s = "appended to arguments" then Append_args
  else Ignore_args

type inputenc = Elocale | Eutf8 | Emanual of string

let string_of_inputenc = function
  |Elocale -> "LOCALE"
  |Eutf8 -> "UTF-8"
  |Emanual s -> s

let inputenc_of_string s =
      (if s = "UTF-8" then Eutf8
       else if s = "LOCALE" then Elocale
       else Emanual s)


(** Hooks *)

let refresh_style_hook = ref (fun () -> ())
let refresh_language_hook = ref (fun () -> ())
let refresh_editor_hook = ref (fun () -> ())
let refresh_toolbar_hook = ref (fun () -> ())
let contextual_menus_on_goal_hook = ref (fun x -> ())
let resize_window_hook = ref (fun () -> ())
let refresh_tabs_hook = ref (fun () -> ())

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
      mutable window_height :int;
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

let use_default_doc_url = "(automatic)"

let current = {
    cmd_coqtop = None;
    cmd_coqc = "coqc";
    cmd_make = "make";
    cmd_coqmakefile = "coq_makefile -o makefile *.v";
    cmd_coqdoc = "coqdoc -q -g";
    cmd_print = "lpr";

    global_auto_revert = false;
    global_auto_revert_delay = 10000;

    auto_save = true;
    auto_save_delay = 10000;
    auto_save_name = "#","#";

    source_language = "coq";
    source_style = "coq_style";

    read_project = Ignore_args;
    project_file_name = "_CoqProject";

    encoding = if Sys.os_type = "Win32" then Eutf8 else Elocale;

    automatic_tactics = ["trivial"; "tauto"; "auto"; "omega";
			 "auto with *"; "intuition" ];

    modifier_for_navigation = "<Control><Alt>";
    modifier_for_templates = "<Control><Shift>";
    modifier_for_tactics = "<Control><Alt>";
    modifier_for_display = "<Alt><Shift>";
    modifiers_valid = "<Alt><Control><Shift>";


    cmd_browse = Flags.browser_cmd_fmt;
    cmd_editor = if Sys.os_type = "Win32" then "NOTEPAD %s" else "emacs %s";

(*    text_font = Pango.Font.from_string "sans 12";*)
    text_font = Pango.Font.from_string (match Coq_config.gtk_platform with
					  |`QUARTZ -> "Arial Unicode MS 11"
					  |_ -> "Monospace 10");

    doc_url = Coq_config.wwwrefman;
    library_url = Coq_config.wwwstdlib;

    show_toolbar = true;
    contextual_menus_on_goal = true;
    window_width = 800;
    window_height = 600;
    query_window_width = 600;
    query_window_height = 400;
(*
    use_utf8_notation = false;
*)
    auto_complete = false;
    stop_before = true;
    reset_on_tab_switch = false;
    vertical_tabs = false;
    opposite_tabs = false;

    background_color = "cornsilk";
    processed_color = "light green";
    processing_color = "light blue";
    error_color = "#FFCCCC";

    dynamic_word_wrap = false;
    show_line_number = false;
    auto_indent = false;
    show_spaces = true;
    show_right_margin = false;
    spaces_instead_of_tabs = true;
    tab_length = 2;
    highlight_current_line = false;

    nanoPG = false;
  }

let save_pref () =
  if not (Sys.file_exists (Minilib.coqide_config_home ()))
  then Unix.mkdir (Minilib.coqide_config_home ()) 0o700;
  let () = try GtkData.AccelMap.save accel_file with _ -> () in
  let p = current in

    let add = Util.String.Map.add in
    let (++) x f = f x in
    Util.String.Map.empty ++
    add "cmd_coqtop" (match p.cmd_coqtop with | None -> [] | Some v-> [v]) ++
    add "cmd_coqc" [p.cmd_coqc] ++
    add "cmd_make" [p.cmd_make] ++
    add "cmd_coqmakefile" [p.cmd_coqmakefile] ++
    add "cmd_coqdoc" [p.cmd_coqdoc] ++
    add "source_language" [p.source_language] ++
    add "source_style" [p.source_style] ++
    add "global_auto_revert" [string_of_bool p.global_auto_revert] ++
    add "global_auto_revert_delay"
      [string_of_int p.global_auto_revert_delay] ++
    add "auto_save" [string_of_bool p.auto_save] ++
    add "auto_save_delay" [string_of_int p.auto_save_delay] ++
    add "auto_save_name" [fst p.auto_save_name; snd p.auto_save_name] ++

    add "project_options" [string_of_project_behavior p.read_project] ++
    add "project_file_name" [p.project_file_name] ++

    add "encoding" [string_of_inputenc p.encoding] ++

    add "automatic_tactics" p.automatic_tactics ++
    add "cmd_print" [p.cmd_print] ++
    add "modifier_for_navigation" [p.modifier_for_navigation] ++
    add "modifier_for_templates" [p.modifier_for_templates] ++
    add "modifier_for_tactics" [p.modifier_for_tactics] ++
    add "modifier_for_display" [p.modifier_for_display] ++
    add "modifiers_valid" [p.modifiers_valid] ++
    add "cmd_browse" [p.cmd_browse] ++
    add "cmd_editor" [p.cmd_editor] ++

    add "text_font" [Pango.Font.to_string p.text_font] ++

    add "doc_url" [p.doc_url] ++
    add "library_url" [p.library_url] ++
    add "show_toolbar" [string_of_bool p.show_toolbar] ++
    add "contextual_menus_on_goal"
      [string_of_bool p.contextual_menus_on_goal] ++
    add "window_height" [string_of_int p.window_height] ++
    add "window_width" [string_of_int p.window_width] ++
    add "query_window_height" [string_of_int p.query_window_height] ++
    add "query_window_width" [string_of_int p.query_window_width] ++
    add "auto_complete" [string_of_bool p.auto_complete] ++
    add "stop_before" [string_of_bool p.stop_before] ++
    add "reset_on_tab_switch" [string_of_bool p.reset_on_tab_switch] ++
    add "vertical_tabs" [string_of_bool p.vertical_tabs] ++
    add "opposite_tabs" [string_of_bool p.opposite_tabs] ++
    add "background_color" [p.background_color] ++
    add "processing_color" [p.processing_color] ++
    add "processed_color" [p.processed_color] ++
    add "error_color" [p.error_color] ++
    add "dynamic_word_wrap" [string_of_bool p.dynamic_word_wrap] ++
    add "show_line_number" [string_of_bool p.show_line_number] ++
    add "auto_indent" [string_of_bool p.auto_indent] ++
    add "show_spaces" [string_of_bool p.show_spaces] ++
    add "show_right_margin" [string_of_bool p.show_right_margin] ++
    add "spaces_instead_of_tabs" [string_of_bool p.spaces_instead_of_tabs] ++
    add "tab_length" [string_of_int p.tab_length] ++
    add "highlight_current_line" [string_of_bool p.highlight_current_line] ++
    add "nanoPG" [string_of_bool p.nanoPG] ++
    Config_lexer.print_file pref_file

let load_pref () =
  let () = try GtkData.AccelMap.load loaded_accel_file with _ -> () in

    let m = Config_lexer.load_file loaded_pref_file in
    let np = current in
    let set k f = try let v = Util.String.Map.find k m in f v with _ -> () in
    let set_hd k f = set k (fun v -> f (List.hd v)) in
    let set_bool k f = set_hd k (fun v -> f (bool_of_string v)) in
    let set_int k f = set_hd k (fun v -> f (int_of_string v)) in
    let set_pair k f = set k (function [v1;v2] -> f v1 v2 | _ -> raise Exit) in
    let set_command_with_pair_compat k f =
      set k (function [v1;v2] -> f (v1^"%s"^v2) | [v] -> f v | _ -> raise Exit)
    in
    let set_option k f = set k (fun v -> f (match v with |[] -> None |h::_ ->  Some h)) in
    set_option "cmd_coqtop" (fun v -> np.cmd_coqtop <- v);
    set_hd "cmd_coqc" (fun v -> np.cmd_coqc <- v);
    set_hd "cmd_make" (fun v -> np.cmd_make <- v);
    set_hd "cmd_coqmakefile" (fun v -> np.cmd_coqmakefile <- v);
    set_hd "cmd_coqdoc" (fun v -> np.cmd_coqdoc <- v);
    set_hd "source_language" (fun v -> np.source_language <- v);
    set_hd "source_style" (fun v -> np.source_style <- v);
    set_bool "global_auto_revert" (fun v -> np.global_auto_revert <- v);
    set_int "global_auto_revert_delay"
      (fun v -> np.global_auto_revert_delay <- v);
    set_bool "auto_save" (fun v -> np.auto_save <- v);
    set_int "auto_save_delay" (fun v -> np.auto_save_delay <- v);
    set_pair "auto_save_name" (fun v1 v2 -> np.auto_save_name <- (v1,v2));
    set_hd "encoding" (fun v -> np.encoding <- (inputenc_of_string v));
    set_hd "project_options"
      (fun v -> np.read_project <- (project_behavior_of_string v));
    set_hd "project_file_name" (fun v -> np.project_file_name <- v);
    set "automatic_tactics"
      (fun v -> np.automatic_tactics <- v);
    set_hd "cmd_print" (fun v -> np.cmd_print <- v);
    set_hd "modifier_for_navigation"
      (fun v -> np.modifier_for_navigation <- v);
    set_hd "modifier_for_templates"
      (fun v -> np.modifier_for_templates <- v);
    set_hd "modifier_for_tactics"
      (fun v -> np.modifier_for_tactics <- v);
    set_hd "modifier_for_display"
      (fun v -> np.modifier_for_display <- v);
    set_hd "modifiers_valid"
      (fun v ->
	np.modifiers_valid <- v);
    set_command_with_pair_compat "cmd_browse" (fun v -> np.cmd_browse <- v);
    set_command_with_pair_compat "cmd_editor" (fun v -> np.cmd_editor <- v);
    set_hd "text_font" (fun v -> np.text_font <- Pango.Font.from_string v);
    set_hd "doc_url" (fun v ->
      if not (Flags.is_standard_doc_url v) &&
        v <> use_default_doc_url &&
	(* Extra hack to support links to last released doc version *)
        v <> Coq_config.wwwcoq ^ "doc" &&
	v <> Coq_config.wwwcoq ^ "doc/"
      then
	(* ("Warning: Non-standard URL for Coq documentation in preference file: "^v);*)
      np.doc_url <- v);
    set_hd "library_url" (fun v -> np.library_url <- v);
    set_bool "show_toolbar" (fun v -> np.show_toolbar <- v);
    set_bool "contextual_menus_on_goal"
      (fun v -> np.contextual_menus_on_goal <- v);
    set_int "window_width" (fun v -> np.window_width <- v);
    set_int "window_height" (fun v -> np.window_height <- v);
    set_int "query_window_width" (fun v -> np.query_window_width <- v);
    set_int "query_window_height" (fun v -> np.query_window_height <- v);
    set_bool "auto_complete" (fun v -> np.auto_complete <- v);
    set_bool "stop_before" (fun v -> np.stop_before <- v);
    set_bool "reset_on_tab_switch" (fun v -> np.reset_on_tab_switch <- v);
    set_bool "vertical_tabs" (fun v -> np.vertical_tabs <- v);
    set_bool "opposite_tabs" (fun v -> np.opposite_tabs <- v);
    set_hd "background_color" (fun v -> np.background_color <- v);
    set_hd "processing_color" (fun v -> np.processing_color <- v);
    set_hd "processed_color" (fun v -> np.processed_color <- v);
    set_hd "error_color" (fun v -> np.error_color <- v);
    set_bool "dynamic_word_wrap" (fun v -> np.dynamic_word_wrap <- v);
    set_bool "show_line_number" (fun v -> np.show_line_number <- v);
    set_bool "auto_indent" (fun v -> np.auto_indent <- v);
    set_bool "show_spaces" (fun v -> np.show_spaces <- v);
    set_bool "show_right_margin" (fun v -> np.show_right_margin <- v);
    set_bool "spaces_instead_of_tabs" (fun v -> np.spaces_instead_of_tabs <- v);
    set_int "tab_length" (fun v -> np.tab_length <- v);
    set_bool "highlight_current_line" (fun v -> np.highlight_current_line <- v);
    set_bool "nanoPG" (fun v -> np.nanoPG <- v);
    ()

let configure ?(apply=(fun () -> ())) () =
  let cmd_coqtop =
    string
      ~f:(fun s -> current.cmd_coqtop <- if s = "AUTO" then None else Some s)
      "       coqtop" (match current.cmd_coqtop with |None -> "AUTO" | Some x -> x) in
  let cmd_coqc =
    string
      ~f:(fun s -> current.cmd_coqc <- s)
      "       coqc"  current.cmd_coqc in
  let cmd_make =
    string
      ~f:(fun s -> current.cmd_make <- s)
      "       make" current.cmd_make in
  let cmd_coqmakefile =
    string
      ~f:(fun s -> current.cmd_coqmakefile <- s)
      "coqmakefile" current.cmd_coqmakefile in
  let cmd_coqdoc =
    string
      ~f:(fun s -> current.cmd_coqdoc <- s)
      "     coqdoc" current.cmd_coqdoc in
  let cmd_print =
    string
      ~f:(fun s -> current.cmd_print <- s)
      "   Print ps" current.cmd_print in

  let config_font =
    let box = GPack.hbox () in
    let w = GMisc.font_selection () in
    w#set_preview_text
      "Goal (∃n : nat, n ≤ 0)∧(∀x,y,z, x∈y⋃z↔x∈y∨x∈z).";
    box#pack ~expand:true w#coerce;
    ignore (w#misc#connect#realize
	      ~callback:(fun () -> w#set_font_name
			   (Pango.Font.to_string current.text_font)));
    custom
      ~label:"Fonts for text"
      box
      (fun () ->
	 let fd =  w#font_name in
	 current.text_font <- (Pango.Font.from_string fd) ;
(*
	 Format.printf "in config_font: current.text_font = %s@." (Pango.Font.to_string current.text_font);
*)
	 !refresh_editor_hook ())
      true
  in

  let config_color =
    let box = GPack.vbox () in
    let table = GPack.table
      ~row_spacings:5
      ~col_spacings:5
      ~border_width:2
      ~packing:(box#pack ~expand:true) ()
    in
    let background_label = GMisc.label
      ~text:"Background color"
      ~packing:(table#attach ~expand:`X ~left:0 ~top:0) ()
    in
    let processed_label = GMisc.label
      ~text:"Background color of processed text"
      ~packing:(table#attach ~expand:`X ~left:0 ~top:1) ()
    in
    let processing_label = GMisc.label
      ~text:"Background color of text being processed"
      ~packing:(table#attach ~expand:`X ~left:0 ~top:2) ()
    in
    let error_label = GMisc.label
      ~text:"Background color of errors"
      ~packing:(table#attach ~expand:`X ~left:0 ~top:3) ()
    in
    let () = background_label#set_xalign 0. in
    let () = processed_label#set_xalign 0. in
    let () = processing_label#set_xalign 0. in
    let () = error_label#set_xalign 0. in
    let background_button = GButton.color_button
      ~color:(Tags.color_of_string (current.background_color))
      ~packing:(table#attach ~left:1 ~top:0) ()
    in
    let processed_button = GButton.color_button
      ~color:(Tags.get_processed_color ())
      ~packing:(table#attach ~left:1 ~top:1) ()
    in
    let processing_button = GButton.color_button
      ~color:(Tags.get_processing_color ())
      ~packing:(table#attach ~left:1 ~top:2) ()
    in
    let error_button = GButton.color_button
      ~color:(Tags.get_error_color ())
      ~packing:(table#attach ~left:1 ~top:3) ()
    in
    let reset_button = GButton.button
      ~label:"Reset"
      ~packing:box#pack ()
    in
    let reset_cb () =
      background_button#set_color (Tags.color_of_string "cornsilk");
      processing_button#set_color (Tags.color_of_string "light blue");
      processed_button#set_color (Tags.color_of_string "light green");
      error_button#set_color (Tags.color_of_string "#FFCCCC");
    in
    let _ = reset_button#connect#clicked ~callback:reset_cb in
    let label = "Color configuration" in
    let callback () =
      current.background_color <- Tags.string_of_color background_button#color;
      current.processing_color <- Tags.string_of_color processing_button#color;
      current.processed_color <- Tags.string_of_color processed_button#color;
      current.error_color <- Tags.string_of_color error_button#color;
      !refresh_editor_hook ();
      Tags.set_processing_color processing_button#color;
      Tags.set_processed_color processed_button#color;
      Tags.set_error_color error_button#color
    in
    custom ~label box callback true
  in

  let config_editor =
    let label = "Editor configuration" in
    let box = GPack.vbox () in
    let gen_button text active =
      GButton.check_button ~label:text ~active ~packing:box#pack () in
    let wrap = gen_button "Dynamic word wrap" current.dynamic_word_wrap in
    let line = gen_button "Show line number" current.show_line_number in
    let auto_indent = gen_button "Auto indentation" current.auto_indent in
    let auto_complete = gen_button "Auto completion" current.auto_complete in
    let show_spaces = gen_button "Show spaces" current.show_spaces in
    let show_right_margin = gen_button "Show right margin" current.show_right_margin in
    let spaces_instead_of_tabs =
      gen_button "Insert spaces instead of tabs"
      current.spaces_instead_of_tabs
    in
    let highlight_current_line =
      gen_button "Highlight current line"
      current.highlight_current_line
    in
    let nanoPG = gen_button "Emacs/PG keybindings (μPG mode)" current.nanoPG in
(*     let lbox = GPack.hbox ~packing:box#pack () in *)
(*     let _ = GMisc.label ~text:"Tab width" *)
(*         ~xalign:0. *)
(*         ~packing:(lbox#pack ~expand:true) () *)
(*     in *)
(*     let tab_width = GEdit.spin_button *)
(*       ~digits:0 ~packing:lbox#pack () *)
(*     in *)
    let callback () =
      current.dynamic_word_wrap <- wrap#active;
      current.show_line_number <- line#active;
      current.auto_indent <- auto_indent#active;
      current.show_spaces <- show_spaces#active;
      current.show_right_margin <- show_right_margin#active;
      current.spaces_instead_of_tabs <- spaces_instead_of_tabs#active;
      current.highlight_current_line <- highlight_current_line#active;
      current.nanoPG <- nanoPG#active;
      current.auto_complete <- auto_complete#active;
(*       current.tab_length <- tab_width#value_as_int; *)
      !refresh_editor_hook ()
    in
    custom ~label box callback true
  in

(*
  let show_toolbar =
    bool
      ~f:(fun s ->
	    current.show_toolbar <- s;
	    !show_toolbar s)
      "Show toolbar" current.show_toolbar
  in
  let window_height =
    string
    ~f:(fun s -> current.window_height <- (try int_of_string s with _ -> 600);
	  !resize_window ();
       )
      "Window height"
      (string_of_int current.window_height)
  in
  let window_width =
    string
    ~f:(fun s -> current.window_width <-
	  (try int_of_string s with _ -> 800))
      "Window width"
      (string_of_int current.window_width)
  in
*)
(*  let use_utf8_notation =
    bool
      ~f:(fun b ->
	    current.use_utf8_notation <- b;
	 )
      "Use Unicode Notation: " current.use_utf8_notation
  in
*)
(*
  let config_appearance = [show_toolbar; window_width; window_height] in
*)
  let global_auto_revert =
    bool
      ~f:(fun s -> current.global_auto_revert <- s)
      "Enable global auto revert" current.global_auto_revert
  in
  let global_auto_revert_delay =
    string
    ~f:(fun s -> current.global_auto_revert_delay <-
	  (try int_of_string s with _ -> 10000))
      "Global auto revert delay (ms)"
      (string_of_int current.global_auto_revert_delay)
  in

  let auto_save =
    bool
      ~f:(fun s -> current.auto_save <- s)
      "Enable auto save" current.auto_save
  in
  let auto_save_delay =
    string
    ~f:(fun s -> current.auto_save_delay <-
	  (try int_of_string s with _ -> 10000))
      "Auto save delay (ms)"
      (string_of_int current.auto_save_delay)
  in

  let stop_before =
    bool
      ~f:(fun s -> current.stop_before <- s)
      "Stop interpreting before the current point" current.stop_before
  in

  let reset_on_tab_switch =
    bool
      ~f:(fun s -> current.reset_on_tab_switch <- s)
      "Reset coqtop on tab switch" current.reset_on_tab_switch
  in

  let vertical_tabs =
    bool
      ~f:(fun s -> current.vertical_tabs <- s; !refresh_tabs_hook ())
      "Vertical tabs" current.vertical_tabs
  in

  let opposite_tabs =
    bool
      ~f:(fun s -> current.opposite_tabs <- s; !refresh_tabs_hook ())
      "Tabs on opposite side" current.opposite_tabs
  in

  let encodings =
    combo
      "File charset encoding "
      ~f:(fun s -> current.encoding <- (inputenc_of_string s))
      ~new_allowed: true
      ("UTF-8"::"LOCALE":: match current.encoding with
	|Emanual s -> [s]
	|_ -> []
      )
      (string_of_inputenc current.encoding)
  in

  let source_style =
    let f s =
      current.source_style <- s;
      !refresh_style_hook ()
    in
    combo "Highlighting style:"
      ~f ~new_allowed:false
      style_manager#style_scheme_ids current.source_style
  in

  let source_language =
    let f s =
      current.source_language <- s;
      !refresh_language_hook ()
    in
    combo "Language:"
      ~f ~new_allowed:false
      (List.filter
        (fun x -> Str.string_match (Str.regexp "^coq") x 0)
        lang_manager#language_ids)
      current.source_language
  in

  let read_project =
    combo
      "Project file options are"
      ~f:(fun s -> current.read_project <- project_behavior_of_string s)
      ~editable:false
      [string_of_project_behavior Subst_args;
       string_of_project_behavior Append_args;
       string_of_project_behavior Ignore_args]
      (string_of_project_behavior current.read_project)
  in
  let project_file_name =
    string "Default name for project file"
      ~f:(fun s -> current.project_file_name <- s)
      current.project_file_name
  in
  let help_string =
    "restart to apply"
  in
  let the_valid_mod = str_to_mod_list current.modifiers_valid in
  let modifier_for_tactics =
    modifiers
      ~allow:the_valid_mod
      ~f:(fun l -> current.modifier_for_tactics <- mod_list_to_str l)
      ~help:help_string
      "Modifiers for Tactics Menu"
      (str_to_mod_list current.modifier_for_tactics)
  in
  let modifier_for_templates =
    modifiers
      ~allow:the_valid_mod
      ~f:(fun l -> current.modifier_for_templates <- mod_list_to_str l)
      ~help:help_string
      "Modifiers for Templates Menu"
      (str_to_mod_list current.modifier_for_templates)
  in
  let modifier_for_navigation =
    modifiers
      ~allow:the_valid_mod
      ~f:(fun l -> current.modifier_for_navigation <- mod_list_to_str l)
      ~help:help_string
      "Modifiers for Navigation Menu"
      (str_to_mod_list current.modifier_for_navigation)
  in
  let modifier_for_display =
    modifiers
      ~allow:the_valid_mod
      ~f:(fun l -> current.modifier_for_display <- mod_list_to_str l)
      ~help:help_string
      "Modifiers for View Menu"
      (str_to_mod_list current.modifier_for_display)
  in
  let modifiers_valid =
    modifiers
      ~f:(fun l ->
	current.modifiers_valid <- mod_list_to_str l)
      "Allowed modifiers"
      the_valid_mod
  in
  let cmd_editor =
    let predefined = [ "emacs %s"; "vi %s"; "NOTEPAD %s" ] in
    combo
      ~help:"(%s for file name)"
      "External editor"
      ~f:(fun s -> current.cmd_editor <- s)
      ~new_allowed: true
      (predefined@[if List.mem current.cmd_editor predefined then ""
                   else current.cmd_editor])
      current.cmd_editor
  in
  let cmd_browse =
    let predefined = [
      Coq_config.browser;
      "netscape -remote \"openURL(%s)\"";
      "mozilla -remote \"openURL(%s)\"";
      "firefox -remote \"openURL(%s,new-windows)\" || firefox %s &";
      "seamonkey -remote \"openURL(%s)\" || seamonkey %s &"
    ] in
    combo
      ~help:"(%s for url)"
      "Browser"
      ~f:(fun s -> current.cmd_browse <- s)
      ~new_allowed: true
      (predefined@[if List.mem current.cmd_browse predefined then ""
                   else current.cmd_browse])
      current.cmd_browse
  in
  let doc_url =
    let predefined = [
      "file://"^(List.fold_left Filename.concat (Coq_config.docdir) ["html";"refman";""]);
      Coq_config.wwwrefman;
      use_default_doc_url
    ] in
    combo
      "Manual URL"
      ~f:(fun s -> current.doc_url <- s)
      ~new_allowed: true
      (predefined@[if List.mem current.doc_url predefined then ""
                   else current.doc_url])
      current.doc_url in
  let library_url =
    let predefined = [
      "file://"^(List.fold_left Filename.concat (Coq_config.docdir) ["html";"stdlib";""]);
      Coq_config.wwwstdlib
    ] in
    combo
      "Library URL"
      ~f:(fun s -> current.library_url <- s)
      ~new_allowed: true
      (predefined@[if List.mem current.library_url predefined then ""
                   else current.library_url])
      current.library_url
  in
  let automatic_tactics =
    strings
      ~f:(fun l -> current.automatic_tactics <- l)
      ~add:(fun () -> ["<edit me>"])
      "Wizard tactics to try in order"
      current.automatic_tactics

  in

  let contextual_menus_on_goal =
    bool
      ~f:(fun s ->
	    current.contextual_menus_on_goal <- s;
	    !contextual_menus_on_goal_hook s)
      "Contextual menus on goal" current.contextual_menus_on_goal
  in

  let misc = [contextual_menus_on_goal;stop_before;reset_on_tab_switch;
              vertical_tabs;opposite_tabs] in

(* ATTENTION !!!!! L'onglet Fonts doit etre en premier pour eviter un bug !!!!
   (shame on Benjamin) *)
  let cmds =
    [Section("Fonts", Some `SELECT_FONT,
	     [config_font]);
     Section("Colors", Some `SELECT_COLOR,
             [config_color; source_language; source_style]);
     Section("Editor", Some `EDIT, [config_editor]);
     Section("Files", Some `DIRECTORY,
	     [global_auto_revert;global_auto_revert_delay;
	      auto_save; auto_save_delay; (* auto_save_name*)
	      encodings;
	     ]);
     Section("Project", Some (`STOCK "gtk-page-setup"),
	     [project_file_name;read_project;
	     ]);
(*
     Section("Appearance",
	     config_appearance);
*)
     Section("Externals", None,
	     [cmd_coqtop;cmd_coqc;cmd_make;cmd_coqmakefile; cmd_coqdoc;
	      cmd_print;cmd_editor;cmd_browse;doc_url;library_url]);
     Section("Tactics Wizard", None,
	     [automatic_tactics]);
     Section("Shortcuts", Some `PREFERENCES,
	     [modifiers_valid; modifier_for_tactics;
	      modifier_for_templates; modifier_for_display; modifier_for_navigation]);
     Section("Misc", Some `ADD,
	     misc)]
  in
(*
  Format.printf "before edit: current.text_font = %s@." (Pango.Font.to_string current.text_font);
*)
  let x = edit ~apply "Customizations" cmds in
(*
  Format.printf "after edit: current.text_font = %s@." (Pango.Font.to_string current.text_font);
*)
  match x with
    | Return_apply | Return_ok -> save_pref ()
    | Return_cancel -> ()
