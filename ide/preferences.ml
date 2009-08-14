(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Configwin
open Printf
open Util

let pref_file = Filename.concat System.home ".coqiderc"

let accel_file = Filename.concat System.home ".coqide.keys"

let mod_to_str (m:Gdk.Tags.modifier) = 
  match m with
    | `MOD1 -> "MOD1"
    | `MOD2 -> "MOD2"
    | `MOD3 -> "MOD3"
    | `MOD4 -> "MOD4"
    | `MOD5 -> "MOD5"
    | `BUTTON1 -> "BUTTON1"
    | `BUTTON2 -> "BUTTON2"
    | `BUTTON3 -> "BUTTON3"
    | `BUTTON4 -> "BUTTON4"
    | `BUTTON5 -> "BUTTON5"
    | `CONTROL -> "CONTROL"
    | `LOCK -> "LOCK"
    | `SHIFT -> "SHIFT"

let (str_to_mod:string -> Gdk.Tags.modifier) =
  function
    | "MOD1" -> `MOD1 
    | "MOD2" -> `MOD2 
    | "MOD3" -> `MOD3 
    | "MOD4" -> `MOD4 
    | "MOD5" -> `MOD5 
    | "BUTTON1" -> `BUTTON1 
    | "BUTTON2" -> `BUTTON2 
    | "BUTTON3" -> `BUTTON3 
    | "BUTTON4" -> `BUTTON4 
    | "BUTTON5" -> `BUTTON5 
    | "CONTROL" -> `CONTROL 
    | "LOCK" -> `LOCK 
    | "SHIFT" -> `SHIFT 
    | s -> `MOD1

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

      mutable encoding_use_locale : bool;
      mutable encoding_use_utf8 : bool;
      mutable encoding_manual : string;

      mutable automatic_tactics : string list;
      mutable cmd_print : string;

      mutable modifier_for_navigation : Gdk.Tags.modifier list;
      mutable modifier_for_templates : Gdk.Tags.modifier list;
      mutable modifier_for_tactics : Gdk.Tags.modifier list;
      mutable modifier_for_display : Gdk.Tags.modifier list;
      mutable modifiers_valid : Gdk.Tags.modifier list;

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
      mutable fold_delay_ms : int;
(*
      mutable use_utf8_notation : bool;
*)
      mutable auto_complete : bool;
      mutable stop_before : bool;
      mutable lax_syntax : bool;
      mutable vertical_tabs : bool;
      mutable opposite_tabs : bool;
}

let use_default_doc_url = "(automatic)"

let (current:pref ref) = 
  ref {
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
    
    encoding_use_locale = true;
    encoding_use_utf8 = false;
    encoding_manual = "ISO_8859-1";

    automatic_tactics = ["trivial"; "tauto"; "auto"; "omega";
			 "auto with *"; "intuition" ];
    
    modifier_for_navigation = [`CONTROL; `MOD1];
    modifier_for_templates = [`CONTROL; `SHIFT];
    modifier_for_tactics = [`CONTROL; `MOD1];
    modifier_for_display = [`MOD1;`SHIFT];
    modifiers_valid = [`SHIFT; `CONTROL; `MOD1];

    
    cmd_browse = Flags.browser_cmd_fmt;
    cmd_editor = if Sys.os_type = "Win32" then "NOTEPAD %s" else "emacs %s";
    
(*    text_font = Pango.Font.from_string "sans 12";*)
    text_font = Pango.Font.from_string "Monospace 10";

    doc_url = Coq_config.wwwrefman;
    library_url = Coq_config.wwwstdlib;
    
    show_toolbar = true;
    contextual_menus_on_goal = true;
    window_width = 800;
    window_height = 600; 
    query_window_width = 600;
    query_window_height = 400;
    fold_delay_ms = 400;
(*
    use_utf8_notation = false;
*)
    auto_complete = false;
    stop_before = true;
    lax_syntax = true;
    vertical_tabs = false;
    opposite_tabs = false;
  }


let change_font = ref (fun f -> ())

let show_toolbar = ref (fun x -> ())

let auto_complete = ref (fun x -> ())

let contextual_menus_on_goal = ref (fun x -> ())

let resize_window = ref (fun () -> ())

let save_pref () =
  (try GtkData.AccelMap.save accel_file 
  with _ -> ());
  let p = !current in
  try 
    let add = Stringmap.add in
    let (++) x f = f x in
    Stringmap.empty ++
    add "cmd_coqc" [p.cmd_coqc] ++
    add "cmd_make" [p.cmd_make] ++
    add "cmd_coqmakefile" [p.cmd_coqmakefile] ++
    add "cmd_coqdoc" [p.cmd_coqdoc] ++
    add "global_auto_revert" [string_of_bool p.global_auto_revert] ++
    add "global_auto_revert_delay" 
      [string_of_int p.global_auto_revert_delay] ++
    add "auto_save" [string_of_bool p.auto_save] ++
    add "auto_save_delay" [string_of_int p.auto_save_delay] ++
    add "auto_save_name" [fst p.auto_save_name; snd p.auto_save_name] ++

    add "encoding_use_locale" [string_of_bool p.encoding_use_locale] ++
    add "encoding_use_utf8" [string_of_bool p.encoding_use_utf8] ++
    add "encoding_manual" [p.encoding_manual] ++

    add "automatic_tactics" p.automatic_tactics ++
    add "cmd_print" [p.cmd_print] ++
    add "modifier_for_navigation" 
      (List.map mod_to_str p.modifier_for_navigation) ++
    add "modifier_for_templates" 
      (List.map mod_to_str p.modifier_for_templates) ++
    add "modifier_for_tactics" 
      (List.map mod_to_str p.modifier_for_tactics) ++
    add "modifier_for_display" 
      (List.map mod_to_str p.modifier_for_display) ++
    add "modifiers_valid" 
      (List.map mod_to_str p.modifiers_valid) ++
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
    add "fold_delay_ms" [string_of_int p.fold_delay_ms] ++
    add "auto_complete" [string_of_bool p.auto_complete] ++
    add "stop_before" [string_of_bool p.stop_before] ++
    add "lax_syntax" [string_of_bool p.lax_syntax] ++
    add "vertical_tabs" [string_of_bool p.vertical_tabs] ++
    add "opposite_tabs" [string_of_bool p.opposite_tabs] ++
    Config_lexer.print_file pref_file
  with _ -> prerr_endline "Could not save preferences."

let load_pref () =
  (try GtkData.AccelMap.load accel_file with _ -> ());
  let p = !current in 
  try 
    let m = Config_lexer.load_file pref_file in
    let np = { p with cmd_coqc = p.cmd_coqc } in
    let set k f = try let v = Stringmap.find k m in f v with _ -> () in
    let set_hd k f = set k (fun v -> f (List.hd v)) in
    let set_bool k f = set_hd k (fun v -> f (bool_of_string v)) in
    let set_int k f = set_hd k (fun v -> f (int_of_string v)) in
    let set_pair k f = set k (function [v1;v2] -> f v1 v2 | _ -> raise Exit) in
    let set_command_with_pair_compat k f = 
      set k (function [v1;v2] -> f (v1^"%s"^v2) | [v] -> f v | _ -> raise Exit)
    in
    set_hd "cmd_coqc" (fun v -> np.cmd_coqc <- v);
    set_hd "cmd_make" (fun v -> np.cmd_make <- v);
    set_hd "cmd_coqmakefile" (fun v -> np.cmd_coqmakefile <- v);
    set_hd "cmd_coqdoc" (fun v -> np.cmd_coqdoc <- v);
    set_bool "global_auto_revert" (fun v -> np.global_auto_revert <- v);
    set_int "global_auto_revert_delay" 
      (fun v -> np.global_auto_revert_delay <- v);
    set_bool "auto_save" (fun v -> np.auto_save <- v);
    set_int "auto_save_delay" (fun v -> np.auto_save_delay <- v);
    set_pair "auto_save_name" (fun v1 v2 -> np.auto_save_name <- (v1,v2));
    set_bool "encoding_use_locale" (fun v -> np.encoding_use_locale <- v);
    set_bool "encoding_use_utf8" (fun v -> np.encoding_use_utf8 <- v);
    set_hd "encoding_manual" (fun v -> np.encoding_manual <- v);
    set "automatic_tactics"
      (fun v -> np.automatic_tactics <- v);
    set_hd "cmd_print" (fun v -> np.cmd_print <- v);
    set "modifier_for_navigation" 
      (fun v -> np.modifier_for_navigation <- List.map str_to_mod v);
    set "modifier_for_templates" 
      (fun v -> np.modifier_for_templates <- List.map str_to_mod v);
    set "modifier_for_tactics" 
      (fun v -> np.modifier_for_tactics <- List.map str_to_mod v);
    set "modifier_for_display" 
      (fun v -> np.modifier_for_display <- List.map str_to_mod v);
    set "modifiers_valid" 
      (fun v -> np.modifiers_valid <- List.map str_to_mod v);
    set_command_with_pair_compat "cmd_browse" (fun v -> np.cmd_browse <- v);
    set_command_with_pair_compat "cmd_editor" (fun v -> np.cmd_editor <- v);
    set_hd "text_font" (fun v -> np.text_font <- Pango.Font.from_string v);
    set_hd "doc_url" (fun v ->
      if not (Flags.is_standard_doc_url v) && v <> use_default_doc_url then
	prerr_endline ("Warning: Non-standard URL for Coq documentation in preference file: "^v);
      np.doc_url <- v);
    set_hd "library_url" (fun v -> np.library_url <- v);
    set_bool "show_toolbar" (fun v -> np.show_toolbar <- v);
    set_bool "contextual_menus_on_goal" 
      (fun v -> np.contextual_menus_on_goal <- v);
    set_int "window_width" (fun v -> np.window_width <- v);
    set_int "window_height" (fun v -> np.window_height <- v);
    set_int "query_window_width" (fun v -> np.query_window_width <- v);
    set_int "query_window_height" (fun v -> np.query_window_height <- v);
    set_int "fold_delay_ms" (fun v -> np.fold_delay_ms <- v);
    set_bool "auto_complete" (fun v -> np.auto_complete <- v);
    set_bool "stop_before" (fun v -> np.stop_before <- v);
    set_bool "lax_syntax" (fun v -> np.lax_syntax <- v);
    set_bool "vertical_tabs" (fun v -> np.vertical_tabs <- v);
    set_bool "opposite_tabs" (fun v -> np.opposite_tabs <- v);
    current := np;
(*
    Format.printf "in load_pref: current.text_font = %s@." (Pango.Font.to_string !current.text_font);
*)
  with e -> 
    prerr_endline ("Could not load preferences ("^
		   (Printexc.to_string e)^").")
    
let split_string_format s =
  try 
    let i = Util.string_index_from s 0 "%s" in
    let pre = (String.sub s 0 i) in
    let post = String.sub s (i+2) (String.length s - i - 2) in
    pre,post
  with Not_found -> s,""

let configure ?(apply=(fun () -> ())) () = 
  let cmd_coqc = 
    string
      ~f:(fun s -> !current.cmd_coqc <- s) 
      "       coqc"  !current.cmd_coqc in
  let cmd_make = 
    string 
      ~f:(fun s -> !current.cmd_make <- s)
      "       make" !current.cmd_make in
  let cmd_coqmakefile = 
    string 
      ~f:(fun s -> !current.cmd_coqmakefile <- s)
      "coqmakefile" !current.cmd_coqmakefile in
  let cmd_coqdoc = 
    string 
      ~f:(fun s -> !current.cmd_coqdoc <- s)
      "     coqdoc" !current.cmd_coqdoc in
  let cmd_print = 
    string 
      ~f:(fun s -> !current.cmd_print <- s) 
      "   Print ps" !current.cmd_print in

  let config_font =
    let box = GPack.hbox () in
    let w = GMisc.font_selection () in
    w#set_preview_text
      "Goal (∃n : nat, n ≤ 0)∧(∀x,y,z, x∈y⋃z↔x∈y∨x∈z).";
    box#pack w#coerce;
    ignore (w#misc#connect#realize 
	      ~callback:(fun () -> w#set_font_name 
			   (Pango.Font.to_string !current.text_font)));
    custom
      ~label:"Fonts for text"
      box
      (fun () -> 
	 let fd =  w#font_name in
	 !current.text_font <- (Pango.Font.from_string fd) ; 
(*
	 Format.printf "in config_font: current.text_font = %s@." (Pango.Font.to_string !current.text_font);
*)
	 !change_font !current.text_font)
      true
  in
(*
  let show_toolbar = 
    bool 
      ~f:(fun s -> 
	    !current.show_toolbar <- s; 
	    !show_toolbar s) 
      "Show toolbar" !current.show_toolbar
  in
  let window_height =
    string
    ~f:(fun s -> !current.window_height <- (try int_of_string s with _ -> 600);
	  !resize_window ();
       ) 
      "Window height" 
      (string_of_int !current.window_height)
  in  
  let window_width =
    string
    ~f:(fun s -> !current.window_width <- 
	  (try int_of_string s with _ -> 800)) 
      "Window width" 
      (string_of_int !current.window_width)
  in  
*)
  let auto_complete = 
    bool 
      ~f:(fun s -> 
	    !current.auto_complete <- s; 
	    !auto_complete s) 
      "Auto Complete" !current.auto_complete
  in

(*  let use_utf8_notation = 
    bool 
      ~f:(fun b -> 
	    !current.use_utf8_notation <- b;
	 ) 
      "Use Unicode Notation: " !current.use_utf8_notation
  in
*)  
(*
  let config_appearance = [show_toolbar; window_width; window_height] in
*)
  let global_auto_revert = 
    bool 
      ~f:(fun s -> !current.global_auto_revert <- s) 
      "Enable global auto revert" !current.global_auto_revert
  in
  let global_auto_revert_delay =
    string
    ~f:(fun s -> !current.global_auto_revert_delay <- 
	  (try int_of_string s with _ -> 10000)) 
      "Global auto revert delay (ms)" 
      (string_of_int !current.global_auto_revert_delay)
  in  

  let auto_save = 
    bool 
      ~f:(fun s -> !current.auto_save <- s) 
      "Enable auto save" !current.auto_save
  in
  let auto_save_delay =
    string
    ~f:(fun s -> !current.auto_save_delay <- 
	  (try int_of_string s with _ -> 10000)) 
      "Auto save delay (ms)" 
      (string_of_int !current.auto_save_delay)
  in  

  let fold_delay_ms =
    string
      ~f:(fun s -> !current.fold_delay_ms <-
                   (try int_of_string s with _ -> 300))
      "double click delay to trigger folding (ms)"
      (string_of_int !current.fold_delay_ms)
  in

  let stop_before =
    bool
      ~f:(fun s -> !current.stop_before <- s)
      "Stop interpreting before the current point" !current.stop_before
  in
    
  let lax_syntax =
    bool
      ~f:(fun s -> !current.lax_syntax <- s)
      "Relax read-only constraint at end of command" !current.lax_syntax
  in

  let vertical_tabs =
    bool
      ~f:(fun s -> !current.vertical_tabs <- s)
      "Vertical tabs" !current.vertical_tabs
  in

  let opposite_tabs =
    bool
      ~f:(fun s -> !current.opposite_tabs <- s)
      "Tabs on opposite side" !current.opposite_tabs
  in

  let encodings = 
    combo 
      "File charset encoding "
      ~f:(fun s -> 
	    match s with
	    | "UTF-8" -> 
		!current.encoding_use_utf8 <- true;
		!current.encoding_use_locale <- false
	    | "LOCALE" ->
		!current.encoding_use_utf8 <- false;
		!current.encoding_use_locale <- true
	    | _ -> 		
		!current.encoding_use_utf8 <- false;
		!current.encoding_use_locale <- false;
		!current.encoding_manual <- s;
	 )
      ~new_allowed: true
      ["UTF-8";"LOCALE";!current.encoding_manual]
      (if !current.encoding_use_utf8 then "UTF-8" 
       else if !current.encoding_use_locale then "LOCALE" else !current.encoding_manual)
  in
  let help_string = 
    "Press a set of modifiers and an extra key together (needs then a restart to apply!)"
  in
  let modifier_for_tactics = 
    modifiers
      ~allow:!current.modifiers_valid
      ~f:(fun l -> !current.modifier_for_tactics <- l)
      ~help:help_string
      "Modifiers for Tactics Menu"
      !current.modifier_for_tactics
  in
  let modifier_for_templates = 
    modifiers
      ~allow:!current.modifiers_valid
      ~f:(fun l -> !current.modifier_for_templates <- l)
      ~help:help_string
      "Modifiers for Templates Menu"
      !current.modifier_for_templates
  in
  let modifier_for_navigation = 
    modifiers
      ~allow:!current.modifiers_valid
      ~f:(fun l -> !current.modifier_for_navigation <- l)
      ~help:help_string
      "Modifiers for Navigation Menu"
      !current.modifier_for_navigation
  in
  let modifier_for_display = 
    modifiers
      ~allow:!current.modifiers_valid
      ~f:(fun l -> !current.modifier_for_display <- l)
      ~help:help_string
      "Modifiers for Display Menu"
      !current.modifier_for_display
  in
  let modifiers_valid = 
    modifiers
      ~f:(fun l -> !current.modifiers_valid <- l)
      "Allowed modifiers"
      !current.modifiers_valid
  in
  let cmd_editor = 
    let predefined = [ "emacs %s"; "vi %s"; "NOTEPAD %s" ] in
    combo
      ~help:"(%s for file name)" 
      "External editor"
      ~f:(fun s -> !current.cmd_editor <- s)
      ~new_allowed: true
      (predefined@[if List.mem !current.cmd_editor predefined then ""
                   else !current.cmd_editor])
      !current.cmd_editor
  in    
  let cmd_browse =
    let predefined = [
      Coq_config.browser;
      "netscape -remote \"openURL(%s)\"";
      "mozilla -remote \"openURL(%s)\"";
      "firefox -remote \"openURL(%s,new-windows)\" || firefox %s &";
      "seamonkey -remote \"openURL(%s)\" || seamonkey %s &";
      "open -a Safari %s &"
    ] in
    combo 
      ~help:"(%s for url)" 
      "Browser"
      ~f:(fun s -> !current.cmd_browse <- s)
      ~new_allowed: true
      (predefined@[if List.mem !current.cmd_browse predefined then ""
                   else !current.cmd_browse])
      !current.cmd_browse
  in    
  let doc_url =
    let predefined = [
      use_default_doc_url
    ] in
    combo
      "Manual URL"
      ~f:(fun s -> !current.doc_url <- s)
      ~new_allowed: true
      (predefined@[if List.mem !current.doc_url predefined then ""
                   else !current.doc_url])
      !current.doc_url in
  let library_url = 
    let predefined = [
      Coq_config.wwwstdlib
    ] in
    combo
      "Library URL"
      ~f:(fun s -> !current.library_url <- s)
      (predefined@[if List.mem !current.library_url predefined then ""
                   else !current.library_url])
      !current.library_url
  in
  let automatic_tactics = 
    strings
      ~f:(fun l -> !current.automatic_tactics <- l) 
      ~add:(fun () -> ["<edit me>"])
      "Wizard tactics to try in order" 
      !current.automatic_tactics

  in

  let contextual_menus_on_goal =
    bool 
      ~f:(fun s -> 
	    !current.contextual_menus_on_goal <- s; 
	    !contextual_menus_on_goal s) 
      "Contextual menus on goal" !current.contextual_menus_on_goal
  in 

  let misc = [contextual_menus_on_goal;auto_complete;stop_before;lax_syntax;
              vertical_tabs;opposite_tabs] in
   
(* ATTENTION !!!!! L'onglet Fonts doit etre en premier pour eviter un bug !!!!
   (shame on Benjamin) *)
  let cmds =
    [Section("Fonts",
	     [config_font]);
     Section("Files",
	     [global_auto_revert;global_auto_revert_delay;
	      auto_save; auto_save_delay; (* auto_save_name*)
	      encodings;
	     ]);     
(*
     Section("Appearance",
	     config_appearance);
*)
     Section("Externals",
	     [cmd_coqc;cmd_make;cmd_coqmakefile; cmd_coqdoc; cmd_print;
	      cmd_editor;
	      cmd_browse;doc_url;library_url]);
     Section("Tactics Wizard",
	     [automatic_tactics]);
     Section("Shortcuts",
	     [modifiers_valid; modifier_for_tactics;
	      modifier_for_templates; modifier_for_display; modifier_for_navigation; fold_delay_ms]);
     Section("Misc",
	     misc)]
  in
(*
  Format.printf "before edit: current.text_font = %s@." (Pango.Font.to_string !current.text_font);
*)
  let x = edit ~apply ~width:500 "Customizations" cmds in
(*
  Format.printf "after edit: current.text_font = %s@." (Pango.Font.to_string !current.text_font);
*)
  match x with 
    | Return_apply | Return_ok -> save_pref ()
    | Return_cancel -> ()
