(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let lang_manager = GSourceView3.source_language_manager ~default:true
let () = lang_manager#set_search_path
  ((Minilib.rocqide_data_dirs ())@lang_manager#search_path)
let style_manager = GSourceView3.source_style_scheme_manager ~default:true
let () = style_manager#set_search_path
  ((Minilib.rocqide_data_dirs ())@style_manager#search_path)

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

class virtual ['a] repr =
object(self)
  method raw_into v = Option.get (self#into [v])
  method raw_from s = List.hd (self#from s)
  method virtual into : string list -> 'a option
  method virtual from : 'a -> string list
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
    let obj = { set; get } in
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
  method repr = repr
end

let stick (pref : 'a preference) (obj : < connect : #GObj.widget_signals ; .. >)
  (cb : 'a -> unit) =
  let _ = cb pref#get in
  let p_id = pref#connect#changed ~callback:(fun v -> cb v) in
  let _ = obj#connect#destroy ~callback:(fun () -> pref#connect#disconnect p_id) in
  ()

(** Useful marshallers *)

let mod_to_str = function
  | `MOD1 -> "<Alt>"
  | `MOD2 -> "<Mod2>"
  | `MOD3 -> "<Mod3>"
  | `MOD4 -> "<Mod4>"
  | `MOD5 -> "<Mod5>"
  | `CONTROL -> "<Control>"
  | `SHIFT -> "<Shift>"
  | `HYPER -> "<Hyper>"
  | `META -> "<Meta>"
  | `SUPER -> "<Super>"
  | `RELEASE | `BUTTON1 | `BUTTON2 | `BUTTON3 | `BUTTON4 | `BUTTON5 | `LOCK -> ""

let mod_list_to_str l = List.fold_left (fun s m -> (mod_to_str m)^s) "" l

let str_to_mod_list s = snd (GtkData.AccelGroup.parse s)

type project_behavior = Ignore_args | Append_args | Subst_args

let string_of_project_behavior = function
  | Ignore_args -> "ignored"
  | Append_args -> "appended to arguments"
  | Subst_args -> "taken instead of arguments"

let project_behavior_of_string = function
  | "taken instead of arguments" -> Subst_args
  | "appended to arguments" -> Append_args
  | _ -> Ignore_args

type inputenc = Elocale | Eutf8 | Emanual of string

let string_of_inputenc = function
  | Elocale -> "LOCALE"
  | Eutf8 -> "UTF-8"
  | Emanual s -> s

let inputenc_of_string = function
  | "UTF-8" -> Eutf8
  | "LOCALE" -> Elocale
  | s -> Emanual s

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
  inherit [string] repr
  method from s = [s]
  method into = function [s] -> Some s | _ -> None
end

let string_pair : (string * string) repr =
object
  inherit [string * string] repr
  method from (s1, s2) = [s1; s2]
  method into = function [s1; s2] -> Some (s1, s2) | _ -> None
end

let string_list : string list repr =
object
  inherit [string list] repr
  method from s = s
  method into s = Some s
end

let string_pair_list (sep : char) : (string * string) list repr =
object
  inherit [(string * string) list] repr
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
  inherit [bool] repr
  method from s = [string_of_bool s]
  method into = function
  | ["true"] -> Some true
  | ["false"] -> Some false
  | _ -> None
end

let int : int repr =
object
  inherit [int] repr
  method from s = [string_of_int s]
  method into = function
  | [i] -> (try Some (int_of_string i) with _ -> None)
  | _ -> None
end

let option (r : 'a repr) : 'a option repr =
object
  inherit ['a option] repr
  method from = function None -> [] | Some v -> "" :: r#from v
  method into = function
  | [] -> Some None
  | "" :: s -> Some (r#into s)
  | _ -> None
end

let custom (from : 'a -> string) (into : string -> 'a) : 'a repr =
object
  inherit ['a] repr
  method! raw_from = from
  method! raw_into = into
  method from x = try [from x] with _ -> []
  method into = function
  | [s] -> (try Some (into s) with _ -> None)
  | _ -> None
end

let tag : tag repr =
let _to s = if s = "" then None else Some s in
let _of = function None -> "" | Some s -> s in
object
  inherit [tag] repr
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
  try Some (get_config_file [Minilib.rocqide_config_home ()] "coqide.bindings")
  with Not_found -> None

let get_unicode_bindings_default_file () =
  let name = "default.bindings" in
  let chk d = Sys.file_exists (Filename.concat d name) in
  try
    let dir = List.find chk (Minilib.rocqide_data_dirs ()) in
    Some (Filename.concat dir name)
  with Not_found -> None

(** Hooks *)

let cmd_rocqtop =
  new preference ~name:["cmd_coqtop"] ~init:None ~repr:Repr.(option string)

let cmd_rocqc =
  new preference ~name:["cmd_coqc"] ~init:"coqc" ~repr:Repr.(string)

let cmd_make =
  new preference ~name:["cmd_make"] ~init:"make" ~repr:Repr.(string)

let cmd_rocqmakefile =
  new preference ~name:["cmd_coqmakefile"] ~init:"coq_makefile -o makefile *.v" ~repr:Repr.(string)

let cmd_rocqdoc =
  new preference ~name:["cmd_coqdoc"] ~init:"coqdoc -q -g" ~repr:Repr.(string)

let source_language =
  new preference ~name:["source_language"] ~init:"coq" ~repr:Repr.(string)

let source_style =
  new preference ~name:["source_style"] ~init:"coq_style" ~repr:Repr.(string)

let global_auto_reload =
  new preference ~name:["global_auto_reload"] ~init:false ~repr:Repr.(bool)

let global_auto_reload_delay =
  new preference ~name:["global_auto_reload_delay"] ~init:10000 ~repr:Repr.(int)

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
  let init = Eutf8 in
  new preference ~name:["encoding"] ~init ~repr

let automatic_tactics =
  let init = ["trivial"; "tauto"; "auto"; "auto with *"; "intuition" ] in
  new preference ~name:["automatic_tactics"] ~init ~repr:Repr.(string_list)

let cmd_print =
  new preference ~name:["cmd_print"] ~init:"lpr" ~repr:Repr.(string)

let attach_modifiers (pref : string preference) ?(filter = Fun.const true) prefix =
  let cb mds =
    let mds = str_to_mod_list mds in
    let change ~path ~key ~modi ~changed =
      if CString.is_prefix prefix path && filter path then
        ignore (GtkData.AccelMap.change_entry ~key ~modi:mds ~replace:true path)
    in
    GtkData.AccelMap.foreach change
  in
  pref#connect#changed ~callback:cb

let select_arch m m_mac =
  (* Gtk's <Primary> maps to <Meta> (i.e. "Command") on Darwin (i.e. Mac),
    <Control> on other architectures; but sometimes, we want more distinction *)
  if Coq_config.arch = "Darwin" then m_mac else m

let modifier_for_navigation =
  new preference ~name:["modifier_for_navigation"]
    ~init:(select_arch "<Alt>" "<Control><Primary>") ~repr:Repr.(string)

let modifier_for_templates =
  new preference ~name:["modifier_for_templates"] ~init:"<Control><Shift>" ~repr:Repr.(string)

let modifier_for_display =
  new preference ~name:["modifier_for_display"]
    ~init:(select_arch "<Alt><Shift>" "<Primary><Shift>")~repr:Repr.(string)

let modifier_for_queries =
  new preference ~name:["modifier_for_queries"] ~init:"<Control><Shift>" ~repr:Repr.(string)

let printopts_item_names = ref []

let attach_modifiers_callback () =
  (* Tell to propagate changes done in preference menu to accel map *)
  (* To be done after the preferences are loaded *)
  let printopts_filter path =
    let after_last_slash_pos = (String.rindex path '/') + 1 in
    let item_name = String.sub path after_last_slash_pos (String.length path - after_last_slash_pos) in
    List.mem item_name !printopts_item_names
  in
  let _ = attach_modifiers modifier_for_display "<Actions>/View/" ~filter:printopts_filter in
  let _ = attach_modifiers modifier_for_navigation "<Actions>/Navigation/" in
  let _ = attach_modifiers modifier_for_templates "<Actions>/Templates/" in
  let _ = attach_modifiers modifier_for_queries "<Actions>/Queries/" in
  ()

let modifiers_valid =
  new preference ~name:["modifiers_valid"]
   (* Note: <Primary> is providing <Meta> (i.e. "Command") for Darwin, i.e. MacOS X *)
    ~init:"<Alt><Control><Shift><Primary>" ~repr:Repr.(string)

let browser_cmd_fmt = Option.default Coq_config.browser (Boot.Util.getenv_rocq "REMOTEBROWSER")

let cmd_browse =
  new preference ~name:["cmd_browse"] ~init:browser_cmd_fmt ~repr:Repr.(string)

let cmd_editor =
  let init = if Sys.os_type = "Win32" then "NOTEPAD %s" else "emacs %s" in
  new preference ~name:["cmd_editor"] ~init ~repr:Repr.(string)

let text_font =
  let init = match Config.gtk_platform with
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

let unicode_binding =
  new preference ~name:["unicode_binding"] ~init:true ~repr:Repr.(bool)

let auto_complete =
  new preference ~name:["auto_complete"] ~init:false ~repr:Repr.(bool)

let auto_complete_delay =
  new preference ~name:["auto_complete_delay"] ~init:250 ~repr:Repr.(int)

let stop_before =
  new preference ~name:["stop_before"] ~init:true ~repr:Repr.(bool)

let reset_on_tab_switch =
  new preference ~name:["reset_on_tab_switch"] ~init:false ~repr:Repr.(bool)

let line_ending =
  let repr = Repr.custom line_end_to_string line_end_of_string in
  new preference ~name:["line_ending"] ~init:`DEFAULT ~repr

let document_tabs_pos =
  new preference ~name:["document_tabs_pos"] ~init:"top" ~repr:Repr.(string)

(* let background_color = *)
(*   new preference ~name:["background_color"] ~init:"cornsilk" ~repr:Repr.(string) *)

let attach_tag (pref : string preference) (tag : GText.tag) f =
  tag#set_property (f pref#get);
  pref#connect#changed ~callback:(fun c -> tag#set_property (f c))

let attach_bg (pref : string preference) (tag : GText.tag) =
  attach_tag pref tag (fun c -> `BACKGROUND c)

let attach_fg (pref : string preference) (tag : GText.tag) =
  attach_tag pref tag (fun c -> `FOREGROUND c)

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
    ("message.prompt", make_tag ~fg:"green" ());
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

let processing_color =
  new preference ~name:["processing_color"] ~init:"light blue" ~repr:Repr.(string)

let incompletely_processed_color =
  new preference ~name:["incompletely_processed_color"] ~init:"light sky blue" ~repr:Repr.(string)

let unjustified_conclusion_color =
  new preference ~name:["unjustified_conclusion_color"] ~init:"gold" ~repr:Repr.(string)

let _ = attach_bg processing_color Tags.Script.to_process
let _ = attach_bg incompletely_processed_color Tags.Script.incomplete
let _ = attach_bg unjustified_conclusion_color Tags.Script.unjustified

let breakpoint_color =
  new preference ~name:["breakpoint_color"] ~init:"#db5860" ~repr:Repr.(string)
let white = (* worth showing on preferences menu?? *)
  new preference ~name:["white"] ~init:"white" ~repr:Repr.(string)

let _ = attach_bg breakpoint_color Tags.Script.breakpoint
let _ = attach_fg white Tags.Script.breakpoint

let db_stopping_point_color =
  new preference ~name:["db_stopping_point_color"] ~init:"#2154a6" ~repr:Repr.(string)

let _ = attach_bg db_stopping_point_color Tags.Script.debugging
let _ = attach_fg white Tags.Script.debugging

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
  new preference ~name:["auto_indent"] ~init:true ~repr:Repr.(bool)

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
  new preference ~name:["highlight_current_line"] ~init:true ~repr:Repr.(bool)

let microPG =
  (* Legacy name in preference is "nanoPG" *)
  new preference ~name:["nanoPG"] ~init:false ~repr:Repr.(bool)

let user_queries =
  new preference ~name:["user_queries"] ~init:[] ~repr:Repr.(string_pair_list '$')

let diffs =
  new preference ~name:["diffs"] ~init:"off" ~repr:Repr.(string)

(** Loading/saving preferences *)

let pref_file = Filename.concat (Minilib.rocqide_config_home ()) "coqiderc"
let accel_file = Filename.concat (Minilib.rocqide_config_home ()) "coqide.keys"

let accel_regex = Str.regexp {|\(; \|\)(gtk_accel_path "\([^""]*\)"|}

exception UnknownFormat

(* Attention: this only works with absolute normalized paths -
   which can be assumed here since the path comes from  Glib.get_user_config_dir *)
let rec mkdir_p path perms =
  if not (Sys.file_exists path)
  then
    let parent = Filename.dirname path in
    if not (Sys.file_exists parent) && parent<>path
    then mkdir_p parent perms
    else Unix.mkdir path perms
  else ()

let save_accel_pref () =
  mkdir_p (Minilib.rocqide_config_home ()) 0o700;
  let tmp_file, fd = Filename.open_temp_file ?perms:(Some 0o644)
    ?temp_dir:(Some (Filename.dirname accel_file))
    "coqide.keys_" "" in
  close_out fd;
  GtkData.AccelMap.save tmp_file;
  (* AccelMap.save writes entries in random order, so sort them: *)
  let fd = open_in tmp_file in
  let map = ref CString.Map.empty in
  let top_lines = ref [] in
  begin
    try
      while true do
        let line = input_line fd in
        if Str.string_match accel_regex line 0 then
          let key = Str.matched_group 2 line in
          map := CString.Map.add key line !map
        else begin
          if not (CString.Map.is_empty !map) then begin
            Minilib.log ("Unknown format for coqide.keys; sorting skipped");
            raise UnknownFormat
          end;
          top_lines := line :: !top_lines
        end
      done
    with
    | UnknownFormat -> close_in fd
    | End_of_file ->
      close_in fd;
      let fd = open_out tmp_file in
      List.iter (fun l -> Printf.fprintf fd "%s\n" l) (List.rev !top_lines);
      CString.Map.iter (fun k l -> Printf.fprintf fd "%s\n" l) !map;
      close_out fd
  end;
  Sys.rename tmp_file accel_file

let save_rc_pref () =
  mkdir_p (Minilib.rocqide_config_home ()) 0o700;
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
    let user_file = get_config_file [Minilib.rocqide_config_home ()] name in
    warn ~delay:2000 ("Loading " ^ user_file);
    try_load_pref_file loader warn user_file
  with Not_found ->
  try
    let system_wide_file = get_config_file (Minilib.rocqide_system_config_dirs ()) name in
    warn ~delay:5000 ("No user " ^ name ^ ", using system wide configuration");
    try_load_pref_file loader warn system_wide_file
  with Not_found ->
  (* Compatibility with oldest versions of RocqIDE (<= 8.4) *)
  try
    let old_user_file = get_config_file [Option.default "" (Glib.get_home_dir ())] ("."^name) in
    warn ~delay:5000 ("No " ^ name ^ ", trying to recover from an older version of RocqIDE");
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
