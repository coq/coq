(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Configwin

let lang_manager = GSourceView3.source_language_manager ~default:true
let () = lang_manager#set_search_path
  ((Minilib.coqide_data_dirs ())@lang_manager#search_path)
let style_manager = GSourceView3.source_style_scheme_manager ~default:true
let () = style_manager#set_search_path
  ((Minilib.coqide_data_dirs ())@style_manager#search_path)

type tag = {
  tag_fg_color : string option;
  tag_bg_color : string option;
  tag_bold : bool;
  tag_italic : bool;
  tag_underline : bool;
  tag_strikethrough : bool;
}


(** Generic preferences *)

type obj = {
  set : string list -> unit;
  get : unit -> string list;
}

let preferences : obj Util.String.Map.t ref = ref Util.String.Map.empty
let unknown_preferences : string list Util.String.Map.t ref = ref Util.String.Map.empty

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
  method reset () = self#set default
  method default = default
end

let stick (pref : 'a preference) (obj : < connect : #GObj.widget_signals ; .. >)
  (cb : 'a -> unit) =
  let _ = cb pref#get in
  let p_id = pref#connect#changed ~callback:(fun v -> cb v) in
  let _ = obj#connect#destroy ~callback:(fun () -> pref#connect#disconnect p_id) in
  ()

(** Useful marshallers *)

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

type line_ending = [ `DEFAULT | `WINDOWS | `UNIX ]

let line_end_of_string = function
| "unix" -> `UNIX
| "windows" -> `WINDOWS
| _ -> `DEFAULT

let line_end_to_string = function
| `UNIX -> "unix"
| `WINDOWS -> "windows"
| `DEFAULT -> "default"

let use_default_doc_url = "(automatic)"

module Repr =
struct

let string : string repr =
object
  method from s = [s]
  method into = function [s] -> Some s | _ -> None
end

let string_pair : (string * string) repr =
object
  method from (s1, s2) = [s1; s2]
  method into = function [s1; s2] -> Some (s1, s2) | _ -> None
end

let string_list : string list repr =
object
  method from s = s
  method into s = Some s
end

let string_pair_list (sep : char) : (string * string) list repr =
object
  val sep' = String.make 1 sep
  method from = CList.map (fun (s1, s2) -> CString.concat sep' [s1; s2])
  method into l =
    try
      Some (CList.map (fun s ->
        let split = String.split_on_char sep s in
        CList.nth split 0, CList.nth split 1) l)
    with Failure _ -> None
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

let custom (from : 'a -> string) (into : string -> 'a) : 'a repr =
object
  method from x = try [from x] with _ -> []
  method into = function
  | [s] -> (try Some (into s) with _ -> None)
  | _ -> None
end

let tag : tag repr =
let _to s = if s = "" then None else Some s in
let _of = function None -> "" | Some s -> s in
object
  method from tag = [
    _of tag.tag_fg_color;
    _of tag.tag_bg_color;
    string_of_bool tag.tag_bold;
    string_of_bool tag.tag_italic;
    string_of_bool tag.tag_underline;
    string_of_bool tag.tag_strikethrough;
  ]
  method into = function
  | [fg; bg; bd; it; ul; st] ->
    (try Some {
      tag_fg_color = _to fg;
      tag_bg_color = _to bg;
      tag_bold = bool_of_string bd;
      tag_italic = bool_of_string it;
      tag_underline = bool_of_string ul;
      tag_strikethrough = bool_of_string st;
      }
    with _ -> None)
  | _ -> None
end

end

let get_config_file dirs name =
  let find_config dir = Sys.file_exists (Filename.concat dir name) in
  let config_dir = List.find find_config dirs in
  Filename.concat config_dir name

let get_unicode_bindings_local_file () =
  try Some (get_config_file [Minilib.coqide_config_home ()] "coqide.bindings")
  with Not_found -> None

let get_unicode_bindings_default_file () =
  let name = "default.bindings" in
  let chk d = Sys.file_exists (Filename.concat d name) in
  try
    let dir = List.find chk (Minilib.coqide_data_dirs ()) in
    Some (Filename.concat dir name)
  with Not_found -> None

(** Hooks *)

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

let auto_save_name =
  new preference ~name:["auto_save_name"] ~init:("#","#") ~repr:Repr.(string_pair)

let read_project =
  let repr = Repr.custom string_of_project_behavior project_behavior_of_string in
  new preference ~name:["read_project"] ~init:Append_args ~repr

let project_file_name =
  new preference ~name:["project_file_name"] ~init:"_CoqProject" ~repr:Repr.(string)

let project_path =
  new preference ~name:["project_path"] ~init:None ~repr:Repr.(option string)

let encoding =
  let repr = Repr.custom string_of_inputenc inputenc_of_string in
  let init = if Sys.os_type = "Win32" then Eutf8 else Elocale in
  new preference ~name:["encoding"] ~init ~repr

let automatic_tactics =
  let init = ["trivial"; "tauto"; "auto"; "omega"; "auto with *"; "intuition" ] in
  new preference ~name:["automatic_tactics"] ~init ~repr:Repr.(string_list)

let cmd_print =
  new preference ~name:["cmd_print"] ~init:"lpr" ~repr:Repr.(string)

let attach_modifiers (pref : string preference) prefix =
  let cb mds =
    let mds = str_to_mod_list mds in
    let change ~path ~key ~modi ~changed =
      if CString.is_sub prefix path 0 then
        ignore (GtkData.AccelMap.change_entry ~key ~modi:mds ~replace:true path)
    in
    GtkData.AccelMap.foreach change
  in
  pref#connect#changed ~callback:cb

let select_arch m m_osx =
  if Coq_config.arch = "Darwin" then m_osx else m

let modifier_for_navigation =
  new preference ~name:["modifier_for_navigation"]
    ~init:(select_arch "<Control>" "<Control><Primary>") ~repr:Repr.(string)

let modifier_for_templates =
  new preference ~name:["modifier_for_templates"] ~init:"<Control><Shift>" ~repr:Repr.(string)

let modifier_for_tactics =
  new preference ~name:["modifier_for_tactics"]
    ~init:(select_arch "<Control><Alt>" "<Control><Primary>") ~repr:Repr.(string)

let modifier_for_display =
  new preference ~name:["modifier_for_display"]
    ~init:(select_arch "<Alt><Shift>" "<Primary><Shift>")~repr:Repr.(string)

let modifier_for_queries =
  new preference ~name:["modifier_for_queries"] ~init:"<Control><Shift>" ~repr:Repr.(string)

let attach_modifiers_callback () =
  (* Tell to propagate changes done in preference menu to accel map *)
  (* To be done after the preferences are loaded *)
  let _ = attach_modifiers modifier_for_navigation "<Actions>/Navigation/" in
  let _ = attach_modifiers modifier_for_templates "<Actions>/Templates/" in
  let _ = attach_modifiers modifier_for_tactics "<Actions>/Tactics/" in
  let _ = attach_modifiers modifier_for_display "<Actions>/View/" in
  let _ = attach_modifiers modifier_for_queries "<Actions>/Queries/" in
  ()

let modifiers_valid =
  new preference ~name:["modifiers_valid"] ~init:"<Alt><Control><Shift>" ~repr:Repr.(string)

let browser_cmd_fmt =
 try
  let coq_netscape_remote_var = "COQREMOTEBROWSER" in
  Sys.getenv coq_netscape_remote_var
 with
  Not_found -> Coq_config.browser

let cmd_browse =
  new preference ~name:["cmd_browse"] ~init:browser_cmd_fmt ~repr:Repr.(string)

let cmd_editor =
  let init = if Sys.os_type = "Win32" then "NOTEPAD %s" else "emacs %s" in
  new preference ~name:["cmd_editor"] ~init ~repr:Repr.(string)

let text_font =
  let init = match Coq_config.gtk_platform with
  | `QUARTZ -> "Arial Unicode MS 11"
  | _ -> "Monospace 10"
  in
  new preference ~name:["text_font"] ~init ~repr:Repr.(string)

let show_toolbar =
  new preference ~name:["show_toolbar"] ~init:true ~repr:Repr.(bool)

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

let line_ending =
  let repr = Repr.custom line_end_to_string line_end_of_string in
  new preference ~name:["line_ending"] ~init:`DEFAULT ~repr

let vertical_tabs =
  new preference ~name:["vertical_tabs"] ~init:false ~repr:Repr.(bool)

let opposite_tabs =
  new preference ~name:["opposite_tabs"] ~init:false ~repr:Repr.(bool)

(* let background_color = *)
(*   new preference ~name:["background_color"] ~init:"cornsilk" ~repr:Repr.(string) *)

let attach_tag (pref : string preference) (tag : GText.tag) f =
  tag#set_property (f pref#get);
  pref#connect#changed ~callback:(fun c -> tag#set_property (f c))

let attach_bg (pref : string preference) (tag : GText.tag) =
  attach_tag pref tag (fun c -> `BACKGROUND c)

let attach_fg (pref : string preference) (tag : GText.tag) =
  attach_tag pref tag (fun c -> `FOREGROUND c)

let processing_color =
  new preference ~name:["processing_color"] ~init:"light blue" ~repr:Repr.(string)

let incompletely_processed_color =
  new preference ~name:["incompletely_processed_color"] ~init:"light sky blue" ~repr:Repr.(string)

let _ = attach_bg processing_color Tags.Script.to_process
let _ = attach_bg incompletely_processed_color Tags.Script.incomplete

let tags = ref Util.String.Map.empty

let list_tags () = !tags

let make_tag ?fg ?bg ?(bold = false) ?(italic = false) ?(underline = false) ?(strikethrough = false) () = {
  tag_fg_color = fg;
  tag_bg_color = bg;
  tag_bold = bold;
  tag_italic = italic;
  tag_underline = underline;
  tag_strikethrough = strikethrough;
}

let create_tag name default =
  let pref = new preference ~name:[name] ~init:default ~repr:Repr.(tag) in
  let set_tag tag =
    begin match pref#get.tag_bg_color with
    | None -> tag#set_property (`BACKGROUND_SET false)
    | Some c ->
      tag#set_property (`BACKGROUND_SET true);
      tag#set_property (`BACKGROUND c)
    end;
    begin match pref#get.tag_fg_color with
    | None -> tag#set_property (`FOREGROUND_SET false)
    | Some c ->
      tag#set_property (`FOREGROUND_SET true);
      tag#set_property (`FOREGROUND c)
    end;
    begin match pref#get.tag_bold with
    | false -> tag#set_property (`WEIGHT_SET false)
    | true ->
      tag#set_property (`WEIGHT_SET true);
      tag#set_property (`WEIGHT `BOLD)
    end;
    begin match pref#get.tag_italic with
    | false -> tag#set_property (`STYLE_SET false)
    | true ->
      tag#set_property (`STYLE_SET true);
      tag#set_property (`STYLE `ITALIC)
    end;
    begin match pref#get.tag_underline with
    | false -> tag#set_property (`UNDERLINE_SET false)
    | true ->
      tag#set_property (`UNDERLINE_SET true);
      tag#set_property (`UNDERLINE `SINGLE)
    end;
    begin match pref#get.tag_strikethrough with
    | false -> tag#set_property (`STRIKETHROUGH_SET false)
    | true ->
      tag#set_property (`STRIKETHROUGH_SET true);
      tag#set_property (`STRIKETHROUGH true)
    end;
  in
  let iter table =
    let tag = GText.tag ~name () in
    table#add tag#as_tag;
    ignore (pref#connect#changed ~callback:(fun _ -> set_tag tag));
    set_tag tag;
  in
  List.iter iter [Tags.Script.table; Tags.Proof.table; Tags.Message.table];
  tags := Util.String.Map.add name pref !tags

(* note these appear to only set the defaults; they don't override
the user selection from the Edit/Preferences/Tags dialog *)
let () =
  let iter (name, tag) = create_tag name tag in
  List.iter iter [
    ("constr.evar", make_tag ());
    ("constr.keyword", make_tag ~fg:"dark green" ());
    ("constr.notation", make_tag ());
    ("constr.path", make_tag ());
    ("constr.reference", make_tag ~fg:"navy"());
    ("constr.type", make_tag ~fg:"#008080" ());
    ("constr.variable", make_tag ());
    ("message.debug", make_tag ());
    ("message.error", make_tag ());
    ("message.warning", make_tag ());
    ("module.definition", make_tag ~fg:"orange red" ~bold:true ());
    ("module.keyword", make_tag ());
    ("tactic.keyword", make_tag ());
    ("tactic.primitive", make_tag ());
    ("tactic.string", make_tag ());
    ("diff.added", make_tag ~bg:"#b6f1c0" ~underline:true ());
    ("diff.removed", make_tag ~bg:"#f6b9c1" ~strikethrough:true ());
    ("diff.added.bg", make_tag ~bg:"#e9feee" ());
    ("diff.removed.bg", make_tag ~bg:"#fce9eb" ());
  ]

let processed_color =
  new preference ~name:["processed_color"] ~init:"light green" ~repr:Repr.(string)

let _ = attach_bg processed_color Tags.Script.processed
let _ = attach_bg processed_color Tags.Proof.highlight

let error_color =
  new preference ~name:["error_color"] ~init:"#FFCCCC" ~repr:Repr.(string)

let _ = attach_bg error_color Tags.Script.error_bg

let error_fg_color =
  new preference ~name:["error_fg_color"] ~init:"red" ~repr:Repr.(string)

let _ = attach_fg error_fg_color Tags.Script.error

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

let microPG =
  (* Legacy name in preference is "nanoPG" *)
  new preference ~name:["nanoPG"] ~init:false ~repr:Repr.(bool)

let user_queries =
  new preference ~name:["user_queries"] ~init:[] ~repr:Repr.(string_pair_list '$')

let diffs =
  new preference ~name:["diffs"] ~init:"off" ~repr:Repr.(string)

class tag_button (box : Gtk.box Gtk.obj) =
object (self)

  inherit GObj.widget box

  val fg_color = GButton.color_button ()
  val fg_unset = GButton.toggle_button ()
  val bg_color = GButton.color_button ()
  val bg_unset = GButton.toggle_button ()
  val bold = GButton.toggle_button ()
  val italic = GButton.toggle_button ()
  val underline = GButton.toggle_button ()
  val strikethrough = GButton.toggle_button ()

  method set_tag tag =
    let track c but set = match c with
    | None -> set#set_active true
    | Some c ->
      set#set_active false;
      but#set_color (Gdk.Color.color_parse c)
    in
    track tag.tag_bg_color bg_color bg_unset;
    track tag.tag_fg_color fg_color fg_unset;
    bold#set_active tag.tag_bold;
    italic#set_active tag.tag_italic;
    underline#set_active tag.tag_underline;
    strikethrough#set_active tag.tag_strikethrough;

  method tag =
    let get but set =
      if set#active then None
      else Some (Gdk.Color.color_to_string but#color)
    in
    {
      tag_bg_color = get bg_color bg_unset;
      tag_fg_color = get fg_color fg_unset;
      tag_bold = bold#active;
      tag_italic = italic#active;
      tag_underline = underline#active;
      tag_strikethrough = strikethrough#active;
    }

  initializer
    let box = new GPack.box box in
    let set_stock button stock =
      let stock = GMisc.image ~stock ~icon_size:`BUTTON () in
      button#set_image stock#coerce
    in
    set_stock fg_unset `CANCEL;
    set_stock bg_unset `CANCEL;
    set_stock bold `BOLD;
    set_stock italic `ITALIC;
    set_stock underline `UNDERLINE;
    set_stock strikethrough `STRIKETHROUGH;
    box#pack fg_color#coerce;
    box#pack fg_unset#coerce;
    box#pack bg_color#coerce;
    box#pack bg_unset#coerce;
    box#pack bold#coerce;
    box#pack italic#coerce;
    box#pack underline#coerce;
    box#pack strikethrough#coerce;
    let cb but obj = obj#set_sensitive (not but#active) in
    let _ = fg_unset#connect#toggled ~callback:(fun () -> cb fg_unset fg_color#misc) in
    let _ = bg_unset#connect#toggled ~callback:(fun () -> cb bg_unset bg_color#misc) in
    ()

end

let tag_button () =
  let box = GPack.hbox () in
  new tag_button (Gobject.unsafe_cast box#as_widget)

(** Loading/saving preferences *)

let pref_file = Filename.concat (Minilib.coqide_config_home ()) "coqiderc"
let accel_file = Filename.concat (Minilib.coqide_config_home ()) "coqide.keys"

let save_accel_pref () =
  if not (Sys.file_exists (Minilib.coqide_config_home ()))
  then Unix.mkdir (Minilib.coqide_config_home ()) 0o700;
  GtkData.AccelMap.save accel_file

let save_rc_pref () =
  if not (Sys.file_exists (Minilib.coqide_config_home ()))
  then Unix.mkdir (Minilib.coqide_config_home ()) 0o700;
  let add = Util.String.Map.add in
  let fold key obj accu = add key (obj.get ()) accu in
  let prefs = Util.String.Map.fold fold !preferences Util.String.Map.empty in
  let prefs = Util.String.Map.fold Util.String.Map.add !unknown_preferences prefs in
  Config_lexer.print_file pref_file prefs

let save_pref () =
  save_accel_pref ();
  save_rc_pref ()

let try_load_pref_file loader warn file =
  try
    loader file
  with
    e -> warn ~delay:5000 ("Could not load " ^ file ^ " ("^Printexc.to_string e^")")

let load_pref_file loader warn name =
  try
    let user_file = get_config_file [Minilib.coqide_config_home ()] name in
    warn ~delay:2000 ("Loading " ^ user_file);
    try_load_pref_file loader warn user_file
  with Not_found ->
  try
    let system_wide_file = get_config_file (Minilib.coqide_system_config_dirs ()) name in
    warn ~delay:5000 ("No user " ^ name ^ ", using system wide configuration");
    try_load_pref_file loader warn system_wide_file
  with Not_found ->
  (* Compatibility with oldest versions of CoqIDE (<= 8.4) *)
  try
    let old_user_file = get_config_file [COption.default "" (Glib.get_home_dir ())] ("."^name) in
    warn ~delay:5000 ("No " ^ name ^ ", trying to recover from an older version of CoqIDE");
    try_load_pref_file loader warn old_user_file
  with Not_found ->
  (* Built-in configuration *)
    warn ~delay:5000 ("No " ^ name ^ ", using default internal configuration")

let load_accel_pref ~warn =
  load_pref_file GtkData.AccelMap.load warn "coqide.keys"

let load_rc_pref ~warn =
  let loader file =
    let m = Config_lexer.load_file file in
    let iter name v =
      if Util.String.Map.mem name !preferences then
        try (Util.String.Map.find name !preferences).set v with _ -> ()
      else unknown_preferences := Util.String.Map.add name v !unknown_preferences
    in
    Util.String.Map.iter iter m in
  load_pref_file loader warn "coqiderc";
  attach_modifiers_callback ()

let load_pref ~warn =
  load_rc_pref ~warn;
  load_accel_pref ~warn

let pstring name p = string ~f:p#set name p#get
let pbool name p = bool ~f:p#set name p#get
let pmodifiers ?(all = false) name p = modifiers
  ?allow:(if all then None else Some (str_to_mod_list modifiers_valid#get))
  ~f:(fun l -> p#set (mod_list_to_str l))
  ~help:"restart to apply"
  name
  (str_to_mod_list p#get)

let configure ?(apply=(fun () -> ())) parent =
  let cmd_coqtop =
    string
      ~f:(fun s -> cmd_coqtop#set (if s = "AUTO" then None else Some s))
      "    coqidetop" (match cmd_coqtop#get with |None -> "AUTO" | Some x -> x) in
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
	      ~callback:(fun () -> w#set_font_name text_font#get));
    custom
      ~label:"Fonts for text"
      box
      (fun () ->
	 let fd =  w#font_name in
	 text_font#set fd)
      true
  in

  let config_color =
    let box = GPack.vbox () in
    let grid = GPack.grid
      ~row_spacings:5
      ~col_spacings:5
      ~border_width:2
      ~packing:(box#pack ~expand:true) ()
    in
    let reset_button = GButton.button
      ~label:"Reset"
      ~packing:box#pack ()
    in
    let iter i (text, pref) =
      let label = GMisc.label
        ~text ~packing:(grid#attach (*~expand:`X*) ~left:0 ~top:i) ()
      in
      let () = label#set_xalign 0. in
      let button = GButton.color_button
        ~color:(Gdk.Color.color_parse pref#get)
        ~packing:(grid#attach ~left:1 ~top:i) ()
      in
      let _ = button#connect#color_set ~callback:begin fun () ->
        pref#set (Gdk.Color.color_to_string button#color)
      end in
      let reset _ =
        pref#reset ();
        button#set_color (Gdk.Color.color_parse pref#get)
      in
      let _ = reset_button#connect#clicked ~callback:reset in
      ()
    in
    let () = Util.List.iteri iter [
(*       ("Background color", background_color); *)
      ("Background color of processed text", processed_color);
      ("Background color of text being processed", processing_color);
      ("Background color of incompletely processed Qed", incompletely_processed_color);
      ("Background color of errors", error_color);
      ("Foreground color of errors", error_fg_color);
    ] in
    let label = "Color configuration" in
    let callback () = () in
    custom ~label box callback true
  in

  let config_tags =
    let box = GPack.vbox () in
    let scroll = GBin.scrolled_window
      ~hpolicy:`NEVER
      ~vpolicy:`AUTOMATIC
      ~packing:(box#pack ~expand:true)
      ()
    in
    let grid = GPack.grid
      ~row_spacings:5
      ~col_spacings:5
      ~border_width:2
      ~packing:scroll#add_with_viewport ()
    in
    let i = ref 0 in
    let cb = ref [] in
    let iter text tag =
      let label = GMisc.label
        ~text ~packing:(grid#attach (*~expand:`X*) ~left:0 ~top:!i) ()
      in
      let () = label#set_xalign 0. in
      let button = tag_button () in
      let callback () = tag#set button#tag in
      button#set_tag tag#get;
      grid#attach ~left:1 ~top:!i button#coerce;
      incr i;
      cb := callback :: !cb;
    in
    let () = Util.String.Map.iter iter !tags in
    let label = "Tag configuration" in
    let callback () = List.iter (fun f -> f ()) !cb in
    custom ~label box callback true
  in

  let config_editor =
    let label = "Editor configuration" in
    let box = GPack.vbox () in
    let button text (pref : bool preference) =
      let active = pref#get in
      let but = GButton.check_button ~label:text ~active ~packing:box#pack () in
      ignore (but#connect#toggled ~callback:(fun () -> pref#set but#active))
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
    let () = button "Emacs/PG keybindings (μPG mode)" microPG in
    let callback () = () in
    custom ~label box callback true
  in

  let window_height =
    string
    ~f:(fun s -> try window_height#set (int_of_string s) with _ -> ())
      "Default window height at starting time"
      (string_of_int window_height#get)
  in

  let window_width =
    string
    ~f:(fun s -> try window_width#set (int_of_string s) with _ -> ())
      "Default window width at starting time"
      (string_of_int window_width#get)
  in

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
      ~f:(fun s -> encoding#set (inputenc_of_string s))
      ~new_allowed: true
      ("UTF-8"::"LOCALE":: match encoding#get with
	|Emanual s -> [s]
	|_ -> []
      )
      (string_of_inputenc encoding#get)
  in

  let line_ending =
    combo
      "EOL character"
      ~f:(fun s -> line_ending#set (line_end_of_string s))
      ~new_allowed:false
      ["unix"; "windows"; "default"]
      (line_end_to_string line_ending#get)
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
      ~f:(fun s -> read_project#set (project_behavior_of_string s))
      ~editable:false
      [string_of_project_behavior Subst_args;
       string_of_project_behavior Append_args;
       string_of_project_behavior Ignore_args]
      (string_of_project_behavior read_project#get)
  in
  let project_file_name = pstring "Default name for project file" project_file_name in
  let modifier_for_tactics =
    pmodifiers "Global change of modifiers for Tactics Menu" modifier_for_tactics
  in
  let modifier_for_templates =
    pmodifiers "Global change of modifiers for Templates Menu" modifier_for_templates
  in
  let modifier_for_navigation =
    pmodifiers "Global change of modifiers for Navigation Menu" modifier_for_navigation
  in
  let modifier_for_display =
    pmodifiers "Global change of modifiers for View Menu" modifier_for_display
  in
  let modifier_for_queries =
    pmodifiers "Global change of modifiers for Queries Menu" modifier_for_queries
  in
  let modifiers_valid =
    pmodifiers ~all:true "Allowed modifiers" modifiers_valid
  in
  let cmd_editor =
    let predefined = [ "emacs %s"; "vi %s"; "NOTEPAD %s" ] in
    combo
      ~help:"(%s for file name)"
      "External editor"
      ~f:cmd_editor#set
      ~new_allowed: true
      (predefined@[if List.mem cmd_editor#get predefined then ""
                   else cmd_editor#get])
      cmd_editor#get
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
      ~f:cmd_browse#set
      ~new_allowed: true
      (predefined@[if List.mem cmd_browse#get predefined then ""
                   else cmd_browse#get])
      cmd_browse#get
  in

  let misc = [stop_before;reset_on_tab_switch;
              vertical_tabs;opposite_tabs] in

(*
  let add_user_query () =
    let input_string l v =
      match GToolbox.input_string ~title:l v with
      | None -> ""
      | Some s -> s
    in
    let q = input_string "User query" "Your query" in
    let k = input_string "Shortcut key" "Shortcut (a single letter)" in
    let q = CString.map (fun c -> if c = '$' then ' ' else c) q in
    (* Anything that is not a simple letter will be ignored. *)
    let k =
      if Int.equal (CString.length k) 1 && Util.is_letter k.[0] then k
      else "" in
    let k = String.uppercase_ascii k in
      [q, k]
  in

  let user_queries =
    list
      ~f:user_queries#set
      (* Disallow same query, key or empty query. *)
      ~eq:(fun (q1, k1) (q2, k2) -> k1 = k2 || q1 = "" || q2 = "" || q1 = q2)
      ~add:add_user_query
      ~titles:["User query"; "Shortcut key"]
      "User queries"
      (fun (q, s) -> [q; s])
      user_queries#get

  in
*)

(* ATTENTION !!!!! L'onglet Fonts doit etre en premier pour eviter un bug !!!!
   (shame on Benjamin) *)
  let cmds =
    [Section("Fonts", Some `SELECT_FONT,
	     [config_font]);
     Section("Colors", Some `SELECT_COLOR,
             [config_color; source_language; source_style]);
     Section("Tags", Some `SELECT_COLOR,
             [config_tags]);
     Section("Editor", Some `EDIT, [config_editor]);
     Section("Files", Some `DIRECTORY,
	     [global_auto_revert;global_auto_revert_delay;
	      auto_save; auto_save_delay; (* auto_save_name*)
	      encodings; line_ending;
	     ]);
     Section("Project", Some (`STOCK "gtk-page-setup"),
	     [project_file_name;read_project;
	     ]);
     Section("Appearance", Some `PREFERENCES, [window_width; window_height]);
     Section("Externals", None,
	     [cmd_coqtop;cmd_coqc;cmd_make;cmd_coqmakefile; cmd_coqdoc;
              cmd_print;cmd_editor;cmd_browse]);
     Section("Shortcuts", Some `PREFERENCES,
	     [modifiers_valid; modifier_for_tactics;
        modifier_for_templates; modifier_for_display; modifier_for_navigation;
        modifier_for_queries (*; user_queries *)]);
     Section("Misc", Some `ADD,
       misc)]
  in
(*
  Format.printf "before edit: current.text_font = %s@." (Pango.Font.to_string current.text_font);
*)
  let x = edit ~apply "Customizations" ~parent cmds in
(*
  Format.printf "after edit: current.text_font = %s@." (Pango.Font.to_string current.text_font);
*)
  match x with
    | Return_apply | Return_ok -> save_pref ()
    | Return_cancel -> ()
