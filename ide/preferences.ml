(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Configwin
open Printf
open Util

let pref_file = 
  try (Filename.concat (Sys.getenv "HOME") ".coqiderc")
  with _ -> ".coqiderc"

let accel_file = 
  try (Filename.concat (Sys.getenv "HOME") ".coqide.keys")
  with _ -> ".coqide.keys"

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

      mutable automatic_tactics : (string * string) list;
      mutable cmd_print : string;

      mutable modifier_for_navigation : Gdk.Tags.modifier list;
      mutable modifier_for_templates : Gdk.Tags.modifier list;
      mutable modifier_for_tactics : Gdk.Tags.modifier list;
      mutable modifiers_valid : Gdk.Tags.modifier list;

      mutable cmd_browse : string * string;

      mutable text_font : Pango.font_description;

      mutable doc_url : string;
      mutable library_url : string;

      mutable show_toolbar : bool;
      mutable window_width : int;
      mutable window_height :int;
      mutable use_utf8_notation : bool;

    }

let (current:pref ref) = 
  ref {
    cmd_coqc = "coqc";
    cmd_make = "make";
    cmd_coqmakefile = "coq_makefile -o Makefile *.v";
    cmd_coqdoc = "coqdoc -q -g";
    cmd_print = "lpr";

    global_auto_revert = false;
    global_auto_revert_delay = 10000;
    
    auto_save = false;
    auto_save_delay = 10000;
    auto_save_name = "#","#";
    
    encoding_use_locale = true;
    encoding_use_utf8 = true;
    encoding_manual = "ISO_8859-1";

    automatic_tactics = ["Progress Trivial.","Trivial.";
			 "Progress Auto.","Auto.";
			 "Tauto.","Tauto.";
			 "Omega.","Omega.";
			 "Progress Auto with *.","Auto with *.";
			 "Progress Intuition.","Intuition.";
			];
    
    modifier_for_navigation = [`CONTROL; `MOD1];
    modifier_for_templates = [`MOD4];
    modifier_for_tactics = [`CONTROL; `MOD1];
    modifiers_valid = [`SHIFT; `CONTROL; `MOD1; `MOD4];

    
    cmd_browse = "netscape -remote \"OpenURL(", ")\"";
    
    text_font = Pango.Font.from_string "Monospace 12";

    doc_url = "http://coq.inria.fr/doc/";
    library_url = "http://coq.inria.fr/library/";
    
    show_toolbar = true;
    window_width = 800;
    window_height = 600; 
    use_utf8_notation = true;
  }


let change_font = ref (fun f -> ())

let show_toolbar = ref (fun x -> ())

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

    add "automatic_tactics" 
      (List.fold_left (fun l (v1,v2) -> v1::v2::l) [] p.automatic_tactics) ++
    add "cmd_print" [p.cmd_print] ++
    add "modifier_for_navigation" 
      (List.map mod_to_str p.modifier_for_navigation) ++
    add "modifier_for_templates" 
      (List.map mod_to_str p.modifier_for_templates) ++
    add "modifier_for_tactics" 
      (List.map mod_to_str p.modifier_for_tactics) ++
    add "modifiers_valid" 
      (List.map mod_to_str p.modifiers_valid) ++
    add "cmd_browse" [fst p.cmd_browse; snd p.cmd_browse] ++

    add "text_font" [Pango.Font.to_string p.text_font] ++

    add "doc_url" [p.doc_url] ++
    add "library_url" [p.library_url] ++
    add "show_toolbar" [string_of_bool p.show_toolbar] ++
    add "window_height" [string_of_int p.window_height] ++
    add "window_width" [string_of_int p.window_width] ++
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
      (fun v -> 
	 let rec from_list = function
	   | [] | [_] -> []
	   | x :: y :: l -> (x,y) :: from_list l 
	 in
	 np.automatic_tactics <- from_list v);
    set_hd "cmd_print" (fun v -> np.cmd_print <- v);
    set "modifier_for_navigation" 
      (fun v -> np.modifier_for_navigation <- List.map str_to_mod v);
    set "modifier_for_templates" 
      (fun v -> np.modifier_for_templates <- List.map str_to_mod v);
    set "modifier_for_tactics" 
      (fun v -> np.modifier_for_tactics <- List.map str_to_mod v);
    set "modifiers_valid" 
      (fun v -> np.modifiers_valid <- List.map str_to_mod v);
    set_pair "cmd_browse" (fun v1 v2 -> np.cmd_browse <- (v1,v2));
    set_hd "text_font" (fun v -> np.text_font <- Pango.Font.from_string v);
    set_hd "doc_url" (fun v -> np.doc_url <- v);
    set_hd "library_url" (fun v -> np.library_url <- v);
    set_bool "show_toolbar" (fun v -> np.show_toolbar <- v);
    set_int "window_width" (fun v -> np.window_width <- v);
    set_int "window_height" (fun v -> np.window_height <- v);

    current := np
  with e -> 
    prerr_endline ("Could not load preferences ("^
		   (Printexc.to_string e)^").")
    

let configure () = 
  let cmd_coqc = 
    string
      ~f:(fun s -> !current.cmd_coqc <- s) "coqc"  !current.cmd_coqc in
  let cmd_make = string ~f:(fun s -> !current.cmd_make <- s)
		   "make" !current.cmd_make in
  let cmd_coqmakefile = string ~f:(fun s -> !current.cmd_coqmakefile <- s)
			  "coqmakefile" !current.cmd_coqmakefile in
  let cmd_coqdoc = string ~f:(fun s -> !current.cmd_coqdoc <- s)
		     "coqdoc" !current.cmd_coqdoc in
  let cmd_print = string ~f:(fun s -> !current.cmd_print <- s) 
		    "Print ps" !current.cmd_print in

  let config_font =
    let box = GPack.hbox () in
    let w = GMisc.font_selection () in
    w#set_preview_text
      "Lemma Truth: ∀ p:Prover, `p < Coq`. Proof. Auto with *. Save."; 
    box#pack w#coerce;
    ignore (w#misc#connect#realize 
	      ~callback:(fun () -> w#set_font_name 
			   (Pango.Font.to_string !current.text_font)));
    custom
      ~label:"Fonts for text"
      box
      (fun () -> match w#font_name with 
	 | None -> () 
	 | Some fd -> !current.text_font <- (Pango.Font.from_string fd) ; !change_font !current.text_font)
      true
  in
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

(*  let use_utf8_notation = 
    bool 
      ~f:(fun b -> 
	    !current.use_utf8_notation <- b;
	 ) 
      "Use Unicode Notation: " !current.use_utf8_notation
  in
*)  
  let config_appearance = [show_toolbar; window_width; window_height] in

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
  let modifier_for_tactics = 
    modifiers
      ~allow:!current.modifiers_valid
      ~f:(fun l -> !current.modifier_for_tactics <- l)
      "Modifiers for Tactics Menu"
      !current.modifier_for_tactics
  in
  let modifier_for_templates = 
    modifiers
      ~allow:!current.modifiers_valid
      ~f:(fun l -> !current.modifier_for_templates <- l)
      "Modifiers for Templates Menu"
      !current.modifier_for_templates
  in
  let modifier_for_navigation = 
    modifiers
      ~allow:!current.modifiers_valid
      ~f:(fun l -> !current.modifier_for_navigation <- l)
      "Modifiers for Navigation Menu"
      !current.modifier_for_navigation
  in
  let modifiers_valid = 
    modifiers
      ~f:(fun l -> !current.modifiers_valid <- l)
      "Allowed modifiers"
      !current.modifiers_valid
  in
  let mod_msg = 
    string
      "Needs restart to apply!"
      ~editable:false
      ""
  in

  let cmd_browse = 
    string
      ~f:(fun s -> 
	    !current.cmd_browse <- 
	    try 
	      let i = String.index s '%' in
	      let pre = (String.sub s 0 i) in
	      if String.length s - 1 = i then 
		pre,""
	      else
		let post = String.sub s (i+2) (String.length s - i - 2) in
		prerr_endline pre;
		prerr_endline post;
		pre,post
	    with Not_found -> s,""
	    )
      "Browse command (%s for url)" 
      ((fst !current.cmd_browse)^"%s"^(snd !current.cmd_browse))
  in    
  let doc_url = 
    string ~f:(fun s -> !current.doc_url <- s) "Documentation URL"  !current.doc_url in
  let library_url = 
    string ~f:(fun s -> !current.library_url <- s) "Library URL"  !current.library_url in

  let automatic_tactics = 
    let box = GPack.hbox () in
    let (w,get_data) = Editable_cells.create !current.automatic_tactics in
    box#add w#coerce;
    custom
      ~label:"Wizzard tactics to try in order"
      box
      (fun () -> let d = get_data () in !current.automatic_tactics <- d)
      true

  in
  let cmds =
    [Section("Fonts",
	     [config_font]);
     Section("Appearance",
	     config_appearance);
     Section("Commands",
	     [cmd_coqc;cmd_make;cmd_coqmakefile; cmd_coqdoc; cmd_print]);
     Section("Files",
	     [global_auto_revert;global_auto_revert_delay;
	     auto_save; auto_save_delay; (* auto_save_name*)
	     encodings
	     ]);
     Section("Browser",
	     [cmd_browse;doc_url;library_url]);
     Section("Tactics Wizzard",
	     [automatic_tactics]);
     Section("Shortcuts",
	     [modifiers_valid; modifier_for_tactics;
	      modifier_for_templates; modifier_for_navigation;mod_msg])]
  in
  match edit ~width:500 "Customizations" cmds
  with 
    | Return_apply | Return_ok -> save_pref ()
    | Return_cancel -> ()
