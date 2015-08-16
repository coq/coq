(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

(** Generic preferences *)

type obj = {
  set : string list -> unit;
  get : unit -> string list;
}

let preferences : obj Util.String.Map.t ref = ref Util.String.Map.empty

class type ['a] repr =
object
  method into : string list -> 'a option
  method from : 'a -> string list
end

class ['a] preference_signals ~(changed : 'a GUtil.signal) =
object
  inherit GUtil.ml_signals [changed#disconnect]
  method changed = changed#connect ~after
end

class ['a] preference ~(name : string list) ~(init : 'a) ~(repr : 'a repr) =
object (self)
  initializer
    let set v = match repr#into v with None -> () | Some s -> self#set s in
    let get () = repr#from self#get in
    let obj = { set = set; get = get; } in
    let name = String.concat "." name in
    if Util.String.Map.mem name !preferences then
      invalid_arg ("Preference " ^ name ^ " already exists")
    else
      preferences := Util.String.Map.add name obj !preferences

  val default = init
  val mutable data = init
  val changed : 'a GUtil.signal = new GUtil.signal ()
  val name : string list = name
  method connect = new preference_signals ~changed
  method get = data
  method set (n : 'a) = data <- n; changed#call n
end

(** Useful marshallers *)

module Repr =
struct

let string : string repr =
object
  method from s = [s]
  method into = function [s] -> Some s | _ -> None
end

let bool : bool repr =
object
  method from s = [string_of_bool s]
  method into = function
  | ["true"] -> Some true
  | ["false"] -> Some false
  | _ -> None
end

let int : int repr =
object
  method from s = [string_of_int s]
  method into = function
  | [i] -> (try Some (int_of_string i) with _ -> None)
  | _ -> None
end

let option (r : 'a repr) : 'a option repr =
object
  method from = function None -> [] | Some v -> "" :: r#from v
  method into = function
  | [] -> Some None
  | "" :: s -> Some (r#into s)
  | _ -> None
end

end

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

let refresh_editor_hook = ref (fun () -> ())

(** New style preferences *)

let cmd_coqtop =
  new preference ~name:["cmd_coqtop"] ~init:None ~repr:Repr.(option string)

let cmd_coqc =
  new preference ~name:["cmd_coqc"] ~init:"coqc" ~repr:Repr.(string)

let cmd_make =
  new preference ~name:["cmd_make"] ~init:"make" ~repr:Repr.(string)

let cmd_coqmakefile =
  new preference ~name:["cmd_coqmakefile"] ~init:"coq_makefile -o makefile *.v" ~repr:Repr.(string)

let cmd_coqdoc =
  new preference ~name:["cmd_coqdoc"] ~init:"coqdoc -q -g" ~repr:Repr.(string)

let source_language =
  new preference ~name:["source_language"] ~init:"coq" ~repr:Repr.(string)

let source_style =
  new preference ~name:["source_style"] ~init:"coq_style" ~repr:Repr.(string)

let global_auto_revert =
  new preference ~name:["global_auto_revert"] ~init:false ~repr:Repr.(bool)

let global_auto_revert_delay =
  new preference ~name:["global_auto_revert_delay"] ~init:10000 ~repr:Repr.(int)

let auto_save =
  new preference ~name:["auto_save"] ~init:true ~repr:Repr.(bool)

let auto_save_delay =
  new preference ~name:["auto_save_delay"] ~init:10000 ~repr:Repr.(int)

(* let auto_save_name =
  new preference ~name:["auto_save_name"] ~init: ~repr:Repr.() *)
(* let read_project =
  new preference ~name:["read_project"] ~init: ~repr:Repr.() *)

let project_file_name =
  new preference ~name:["project_file_name"] ~init:"_CoqProject" ~repr:Repr.(string)

let project_path =
  new preference ~name:["project_path"] ~init:None ~repr:Repr.(option string)

(* let encoding =
  new preference ~name:["encoding"] ~init: ~repr:Repr.() *)
(* let automatic_tactics =
  new preference ~name:["automatic_tactics"] ~init: ~repr:Repr.() *)

let cmd_print =
  new preference ~name:["cmd_print"] ~init:"lpr" ~repr:Repr.(string)

let modifier_for_navigation =
  new preference ~name:["modifier_for_navigation"] ~init:"<Control><Alt>" ~repr:Repr.(string)

let modifier_for_templates =
  new preference ~name:["modifier_for_templates"] ~init:"<Control><Shift>" ~repr:Repr.(string)
 
let modifier_for_tactics =
  new preference ~name:["modifier_for_tactics"] ~init:"<Control><Alt>" ~repr:Repr.(string)

let modifier_for_display =
  new preference ~name:["modifier_for_display"] ~init:"<Alt><Shift>" ~repr:Repr.(string)

let modifiers_valid =
  new preference ~name:["modifiers_valid"] ~init:"<Alt><Control><Shift>" ~repr:Repr.(string)

(* let cmd_browse =
  new preference ~name:["cmd_browse"] ~init: ~repr:Repr.() *)
(* let cmd_editor =
  new preference ~name:["cmd_editor"] ~init: ~repr:Repr.() *)
(* let text_font =
  new preference ~name:["text_font"] ~init: ~repr:Repr.() *)
(* let doc_url =
  new preference ~name:["doc_url"] ~init: ~repr:Repr.() *)

let library_url =
  new preference ~name:["library_url"] ~init:Coq_config.wwwstdlib ~repr:Repr.(string)

let show_toolbar =
  new preference ~name:["show_toolbar"] ~init:true ~repr:Repr.(bool)

let contextual_menus_on_goal =
  new preference ~name:["contextual_menus_on_goal"] ~init:true ~repr:Repr.(bool)

let window_width =
  new preference ~name:["window_width"] ~init:800 ~repr:Repr.(int)

let window_height =
  new preference ~name:["window_height"] ~init:600 ~repr:Repr.(int)

let auto_complete =
  new preference ~name:["auto_complete"] ~init:false ~repr:Repr.(bool)

let stop_before =
  new preference ~name:["stop_before"] ~init:true ~repr:Repr.(bool)

let reset_on_tab_switch =
  new preference ~name:["reset_on_tab_switch"] ~init:false ~repr:Repr.(bool)

let vertical_tabs =
  new preference ~name:["vertical_tabs"] ~init:false ~repr:Repr.(bool)

let opposite_tabs =
  new preference ~name:["opposite_tabs"] ~init:false ~repr:Repr.(bool)

let background_color =
  new preference ~name:["background_color"] ~init:Tags.default_color ~repr:Repr.(string)

let processing_color =
  new preference ~name:["processing_color"] ~init:Tags.default_processing_color ~repr:Repr.(string)

let processed_color =
  new preference ~name:["processed_color"] ~init:Tags.default_processed_color ~repr:Repr.(string)

let error_color =
  new preference ~name:["error_color"] ~init:Tags.default_error_color ~repr:Repr.(string)

let error_fg_color =
  new preference ~name:["error_fg_color"] ~init:Tags.default_error_fg_color ~repr:Repr.(string)

let dynamic_word_wrap =
  new preference ~name:["dynamic_word_wrap"] ~init:false ~repr:Repr.(bool)

let show_line_number =
  new preference ~name:["show_line_number"] ~init:false ~repr:Repr.(bool)

let auto_indent =
  new preference ~name:["auto_indent"] ~init:false ~repr:Repr.(bool)

let show_spaces =
  new preference ~name:["show_spaces"] ~init:true ~repr:Repr.(bool)

let show_right_margin =
  new preference ~name:["show_right_margin"] ~init:false ~repr:Repr.(bool)

let show_progress_bar =
  new preference ~name:["show_progress_bar"] ~init:true ~repr:Repr.(bool)

let spaces_instead_of_tabs =
  new preference ~name:["spaces_instead_of_tabs"] ~init:true ~repr:Repr.(bool)

let tab_length =
  new preference ~name:["tab_length"] ~init:2 ~repr:Repr.(int)

let highlight_current_line =
  new preference ~name:["highlight_current_line"] ~init:false ~repr:Repr.(bool)

let nanoPG =
  new preference ~name:["nanoPG"] ~init:false ~repr:Repr.(bool)

(** Old style preferences *)

type pref =
    {

      mutable auto_save_name : string * string;

      mutable read_project : project_behavior;

      mutable encoding : inputenc;

      mutable automatic_tactics : string list;

      mutable cmd_browse : string;
      mutable cmd_editor : string;

      mutable text_font : Pango.font_description;

      mutable doc_url : string;

}

let use_default_doc_url = "(automatic)"

let current = {

    auto_save_name = "#","#";

    read_project = Append_args;

    encoding = if Sys.os_type = "Win32" then Eutf8 else Elocale;

    automatic_tactics = ["trivial"; "tauto"; "auto"; "omega";
			 "auto with *"; "intuition" ];

    cmd_browse = Flags.browser_cmd_fmt;
    cmd_editor = if Sys.os_type = "Win32" then "NOTEPAD %s" else "emacs %s";

(*    text_font = Pango.Font.from_string "sans 12";*)
    text_font = Pango.Font.from_string (match Coq_config.gtk_platform with
					  |`QUARTZ -> "Arial Unicode MS 11"
					  |_ -> "Monospace 10");

    doc_url = Coq_config.wwwrefman;
  }

let save_pref () =
  if not (Sys.file_exists (Minilib.coqide_config_home ()))
  then Unix.mkdir (Minilib.coqide_config_home ()) 0o700;
  let () = try GtkData.AccelMap.save accel_file with _ -> () in
  let p = current in
  let add = Util.String.Map.add in
  let (++) x f = f x in
  let fold key obj accu = add key (obj.get ()) accu in
 
    (Util.String.Map.fold fold !preferences Util.String.Map.empty) ++
    add "auto_save_name" [fst p.auto_save_name; snd p.auto_save_name] ++

    add "project_options" [string_of_project_behavior p.read_project] ++

    add "encoding" [string_of_inputenc p.encoding] ++

    add "automatic_tactics" p.automatic_tactics ++
    add "cmd_browse" [p.cmd_browse] ++
    add "cmd_editor" [p.cmd_editor] ++

    add "text_font" [Pango.Font.to_string p.text_font] ++

    add "doc_url" [p.doc_url] ++
    Config_lexer.print_file pref_file

let load_pref () =
  let () = try GtkData.AccelMap.load loaded_accel_file with _ -> () in

    let m = Config_lexer.load_file loaded_pref_file in
    let iter name v =
      try (Util.String.Map.find name !preferences).set v
      with _ -> ()
    in
    let () = Util.String.Map.iter iter m in
    let np = current in
    let set k f = try let v = Util.String.Map.find k m in f v with _ -> () in
    let set_hd k f = set k (fun v -> f (List.hd v)) in
    let set_pair k f = set k (function [v1;v2] -> f v1 v2 | _ -> raise Exit) in
    let set_command_with_pair_compat k f =
      set k (function [v1;v2] -> f (v1^"%s"^v2) | [v] -> f v | _ -> raise Exit)
    in
    set_pair "auto_save_name" (fun v1 v2 -> np.auto_save_name <- (v1,v2));
    set_hd "encoding" (fun v -> np.encoding <- (inputenc_of_string v));
    set_hd "project_options"
      (fun v -> np.read_project <- (project_behavior_of_string v));
    set "automatic_tactics"
      (fun v -> np.automatic_tactics <- v);
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
    ()

let pstring name p = string ~f:p#set name p#get
let pbool name p = bool ~f:p#set name p#get
let pmodifiers ?(all = false) name p = modifiers
  ?allow:(if all then None else Some (str_to_mod_list modifiers_valid#get))
  ~f:(fun l -> p#set (mod_list_to_str l))
  ~help:"restart to apply"
  name
  (str_to_mod_list p#get)

let configure ?(apply=(fun () -> ())) () =
  let cmd_coqtop =
    string
      ~f:(fun s -> cmd_coqtop#set (if s = "AUTO" then None else Some s))
      "       coqtop" (match cmd_coqtop#get with |None -> "AUTO" | Some x -> x) in
  let cmd_coqc = pstring "       coqc" cmd_coqc in
  let cmd_make = pstring "       make" cmd_make in
  let cmd_coqmakefile = pstring "coqmakefile" cmd_coqmakefile in
  let cmd_coqdoc = pstring "     coqdoc" cmd_coqdoc in
  let cmd_print = pstring "   Print ps" cmd_print in

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
    let error_fg_label = GMisc.label
      ~text:"Foreground color of errors"
      ~packing:(table#attach ~expand:`X ~left:0 ~top:4) ()
    in
    let () = background_label#set_xalign 0. in
    let () = processed_label#set_xalign 0. in
    let () = processing_label#set_xalign 0. in
    let () = error_label#set_xalign 0. in
    let () = error_fg_label#set_xalign 0. in
    let background_button = GButton.color_button
      ~color:(Tags.color_of_string (background_color#get))
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
    let error_fg_button = GButton.color_button
      ~color:(Tags.get_error_fg_color ())
      ~packing:(table#attach ~left:1 ~top:4) ()
    in
    let reset_button = GButton.button
      ~label:"Reset"
      ~packing:box#pack ()
    in
    let reset_cb () =
      background_button#set_color Tags.(color_of_string default_color);
      processing_button#set_color Tags.(color_of_string default_processing_color);
      processed_button#set_color Tags.(color_of_string default_processed_color);
      error_button#set_color Tags.(color_of_string default_error_color);
    in
    let _ = reset_button#connect#clicked ~callback:reset_cb in
    let label = "Color configuration" in
    let callback () =
      background_color#set (Tags.string_of_color background_button#color);
      processing_color#set (Tags.string_of_color processing_button#color);
      processed_color#set (Tags.string_of_color processed_button#color);
      error_color#set (Tags.string_of_color error_button#color);
      error_fg_color#set (Tags.string_of_color error_fg_button#color);
      !refresh_editor_hook ();
      Tags.set_processing_color processing_button#color;
      Tags.set_processed_color processed_button#color;
      Tags.set_error_color error_button#color;
      Tags.set_error_fg_color error_fg_button#color
    in
    custom ~label box callback true
  in

  let config_editor =
    let label = "Editor configuration" in
    let box = GPack.vbox () in
    let button text (pref : bool preference) =
      let active = pref#get in
      let but = GButton.check_button ~label:text ~active ~packing:box#pack () in
      ignore (but#connect#toggled (fun () -> pref#set but#active))
    in
    let () = button "Dynamic word wrap" dynamic_word_wrap in
    let () = button "Show line number" show_line_number in
    let () = button "Auto indentation" auto_indent in
    let () = button "Auto completion" auto_complete in
    let () = button "Show spaces" show_spaces in
    let () = button "Show right margin" show_right_margin in
    let () = button "Show progress bar" show_progress_bar in
    let () = button "Insert spaces instead of tabs" spaces_instead_of_tabs in
    let () = button "Highlight current line" highlight_current_line in
    let () = button "Emacs/PG keybindings (μPG mode)" nanoPG in
    let callback () = !refresh_editor_hook () in
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
(*
  let config_appearance = [show_toolbar; window_width; window_height] in
*)
  let global_auto_revert = pbool "Enable global auto revert" global_auto_revert in
  let global_auto_revert_delay =
    string
    ~f:(fun s -> global_auto_revert_delay#set
	  (try int_of_string s with _ -> 10000))
      "Global auto revert delay (ms)"
      (string_of_int global_auto_revert_delay#get)
  in

  let auto_save = pbool "Enable auto save" auto_save in
  let auto_save_delay =
    string
    ~f:(fun s -> auto_save_delay#set
	  (try int_of_string s with _ -> 10000))
      "Auto save delay (ms)"
      (string_of_int auto_save_delay#get)
  in

  let stop_before = pbool "Stop interpreting before the current point" stop_before in

  let reset_on_tab_switch = pbool "Reset coqtop on tab switch" reset_on_tab_switch in

  let vertical_tabs = pbool "Vertical tabs" vertical_tabs in

  let opposite_tabs = pbool "Tabs on opposite side" opposite_tabs in

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
    combo "Highlighting style:"
      ~f:source_style#set ~new_allowed:false
      style_manager#style_scheme_ids source_style#get
  in

  let source_language =
    combo "Language:"
      ~f:source_language#set ~new_allowed:false
      (List.filter
        (fun x -> Str.string_match (Str.regexp "^coq") x 0)
        lang_manager#language_ids)
      source_language#get
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
  let project_file_name = pstring "Default name for project file" project_file_name in
  let modifier_for_tactics =
    pmodifiers "Modifiers for Tactics Menu" modifier_for_tactics
  in
  let modifier_for_templates =
    pmodifiers "Modifiers for Templates Menu" modifier_for_templates
  in
  let modifier_for_navigation =
    pmodifiers "Modifiers for Navigation Menu" modifier_for_navigation
  in
  let modifier_for_display =
    pmodifiers "Modifiers for View Menu" modifier_for_display
  in
  let modifiers_valid =
    pmodifiers ~all:true "Allowed modifiers" modifiers_valid
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
      ~f:(fun s -> library_url#set s)
      ~new_allowed: true
      (predefined@[if List.mem library_url#get predefined then ""
                   else library_url#get])
      library_url#get
  in
  let automatic_tactics =
    strings
      ~f:(fun l -> current.automatic_tactics <- l)
      ~add:(fun () -> ["<edit me>"])
      "Wizard tactics to try in order"
      current.automatic_tactics

  in

  let contextual_menus_on_goal = pbool "Contextual menus on goal" contextual_menus_on_goal in

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
