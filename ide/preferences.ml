open Configwin
open Printf

let pref_file = 
  try (Filename.concat (Sys.getenv "HOME") ".coqidepref")
  with _ -> ".coqidepref"

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
      mutable auto_save_name : string*string;

      mutable automatic_tactics : (string * string) list;
      mutable cmd_print : string;

      mutable modifier_for_navigation : Gdk.Tags.modifier list;
      mutable modifier_for_templates : Gdk.Tags.modifier list;
      
      mutable cmd_browse : string * string;

      mutable doc_url : string;
      mutable library_url : string;
    }

let save_pref p =
  try 
    let fd = open_out pref_file in
    let output_string f c = fprintf fd "%s = \"%s\"\n" f c in
    let output_bool f c = fprintf fd "%s = \"%b\"\n" f c in
    let output_int f c = fprintf fd "%s = \"%d\"\n" f c in
    let output_list f to_string l = 
      fprintf fd "%s = [%a]\n" f 
	(fun c -> 
	   List.iter
	   (fun x -> fprintf c "%a;" to_string x)) l in
    let output_modi fd m = fprintf fd "%s" (mod_to_str m) 
    in 
    output_string "cmd_coqc" p.cmd_coqc;
    output_string "cmd_make" p.cmd_make;
    output_string "cmd_coqmakefile" p.cmd_coqmakefile;
    output_string "cmd_coqdoc" p.cmd_coqdoc;
    output_string "cmd_print" p.cmd_print;
    
    output_bool "global_auto_revert" p.global_auto_revert;
    output_int "global_auto_revert_delay" p.global_auto_revert_delay;

    output_bool "auto_save" p.auto_save;
    output_int "auto_save_delay" p.auto_save_delay;
    output_string "auto_save_prefix" (fst p.auto_save_name);
    output_string "auto_save_suffix" (snd p.auto_save_name);

    output_string "cmd_browse_prefix" (fst p.cmd_browse);
    output_string "cmd_browse_suffix" (snd p.cmd_browse);

    output_string "doc_url" p.doc_url;
    output_string "library_url" p.library_url;
    output_list 
      "modifier_for_navigation" 
      output_modi 
      p.modifier_for_navigation;
    output_list 
      "modifier_for_templates" 
      output_modi 
      p.modifier_for_templates;
    close_out fd
  with _ -> prerr_endline "Could not save preferences."
  
let (current:pref) = 
  {
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

    automatic_tactics = [];
    
    modifier_for_navigation = [`CONTROL; `MOD1];
    modifier_for_templates = [`MOD4];
    
    cmd_browse = "netscape -remote \"OpenURL(", ")\"";

    doc_url = "http://coq.inria.fr/doc/";
    library_url = "http://coq.inria.fr/library/";
 }

let load_pref p = 
  try 
    let l = Config_lexer.get_config pref_file in
    List.iter 
      (function k,v -> try match k with
	 | "cmd_coqc" -> p.cmd_coqc <- v
       | "cmd_make" -> p.cmd_make <-  v
       | "cmd_coqmakefile" -> p.cmd_coqmakefile <- v
       | "cmd_coqdoc" -> p.cmd_coqdoc <-  v
       | "cmd_print" -> p.cmd_print <-  v
       | "global_auto_revert" -> p.global_auto_revert <- bool_of_string v
       | "global_auto_revert_delay" -> 
	   p.global_auto_revert_delay <- int_of_string v
       | "auto_save" -> p.auto_save <- bool_of_string v
       | "auto_save_delay" -> p.auto_save_delay <- int_of_string v
       | "auto_save_prefix" -> 
	   let x,y = p.auto_save_name in
	   p.auto_save_name <- (v,y)
       | "auto_save_suffix" -> 
	   let x,y = p.auto_save_name in
	   p.auto_save_name <- (x,v)

       | "cmd_browse_prefix" -> 
	   let x,y = p.cmd_browse in
	   p.cmd_browse <- (v,y)
       | "cmd_browse_suffix" ->
	   let x,y = p.cmd_browse in
	   p.cmd_browse <- (x,v)
       | "doc_url" -> p.doc_url <- v
       | "library_url" -> p.library_url <- v
       | "modifier_for_navigation" ->
	   p.modifier_for_navigation <- 
	   List.rev_map str_to_mod (Config_lexer.split v)
       | "modifier_for_templates" ->
	   p.modifier_for_templates <- 
	   List.rev_map str_to_mod (Config_lexer.split v)
       | _ -> prerr_endline ("Warning: unknown option "^k)
     with _ -> ())
    l
  with _ -> prerr_endline "Could not load preferences."

let configure () = 
  let cmd_coqc = 
    string ~f:(fun s -> current.cmd_coqc <- s) "coqc"  current.cmd_coqc in
  let cmd_make = string ~f:(fun s -> current.cmd_make <- s)
		   "make" current.cmd_make in
  let cmd_coqmakefile = string ~f:(fun s -> current.cmd_coqmakefile <- s)
			  "coqmakefile" current.cmd_coqmakefile in
  let cmd_coqdoc = string ~f:(fun s -> current.cmd_coqdoc <- s)
		     "coqdoc" current.cmd_coqdoc in
  let cmd_print = string ~f:(fun s -> current.cmd_print <- s) 
		    "Print ps" current.cmd_print in

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
  let cmds =
      [Section(
	 "Commands",
	 [cmd_coqc;cmd_make;cmd_coqmakefile; cmd_coqdoc; cmd_print]);
       Section ("Files",
		[global_auto_revert;global_auto_revert_delay])]
  in
  match edit "Customizations" cmds
  with | Return_apply | Return_ok -> save_pref current
    | Return_cancel -> ()
