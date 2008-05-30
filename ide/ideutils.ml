(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)


open Preferences

exception Forbidden

(* status bar and locations *)

let status = ref None
let push_info = ref (function s -> failwith "not ready")
let pop_info = ref (function s -> failwith "not ready")
let flash_info = ref  (fun ?delay s -> failwith "not ready")

let set_location = ref  (function s -> failwith "not ready")

let pulse = ref (function () -> failwith "not ready")


let debug = Flags.debug

let prerr_endline s =
  if !debug then (prerr_endline s;flush stderr)
let prerr_string s =
  if !debug then (prerr_string s;flush stderr)

let lib_ide_file f =
  let coqlib =
    System.getenv_else "COQLIB"
      (if Coq_config.local || !Flags.boot then Coq_config.coqtop
       else Coq_config.coqlib) in
  Filename.concat (Filename.concat coqlib "ide") f
  
let get_insert input_buffer = input_buffer#get_iter_at_mark `INSERT

let is_char_start c = let code = Char.code c in code < 0x80 || code >= 0xc0

let byte_offset_to_char_offset s byte_offset = 
  if (byte_offset < String.length s) then begin
    let count_delta = ref 0 in
    for i = 0 to byte_offset do
      let code = Char.code s.[i] in
      if code >= 0x80 && code < 0xc0 then incr count_delta
    done;
    byte_offset - !count_delta
  end
  else begin
    let count_delta = ref 0 in
    for i = 0 to String.length s - 1 do
      let code = Char.code s.[i] in
      if code >= 0x80 && code < 0xc0 then incr count_delta
    done;
    byte_offset - !count_delta
  end

let print_id id =
  prerr_endline ("GOT sig id :"^(string_of_int (Obj.magic id)))


let do_convert s = 
  Utf8_convert.f
    (if Glib.Utf8.validate s then begin
       prerr_endline "Input is UTF-8";s
     end else
       let from_loc () = 
	 let _,char_set = Glib.Convert.get_charset () in
	 !flash_info
	   ("Converting from locale ("^char_set^")");
	 Glib.Convert.convert_with_fallback ~to_codeset:"UTF-8" ~from_codeset:char_set s
       in
       let from_manual () = 
	 !flash_info 
	   ("Converting from "^ !current.encoding_manual);
	 Glib.Convert.convert s ~to_codeset:"UTF-8" ~from_codeset:!current.encoding_manual
       in
       if !current.encoding_use_utf8 || !current.encoding_use_locale then begin
	 try
	   from_loc ()
	 with _ -> from_manual ()
       end else begin
	 try
	   from_manual () 
	 with _ -> from_loc ()
       end)

let try_convert s = 
  try
    do_convert s
  with _ -> 
    "(* Fatal error: wrong encoding in input.
Please choose a correct encoding in the preference panel.*)";;


let try_export file_name s = 
  try let s = 
    try if !current.encoding_use_utf8 then begin
      (prerr_endline "UTF-8 is enforced" ;s)
    end else if !current.encoding_use_locale then begin
      let is_unicode,char_set = Glib.Convert.get_charset () in
      if is_unicode then 
	(prerr_endline "Locale is UTF-8" ;s)	
      else
	(prerr_endline ("Locale is "^char_set);
	 Glib.Convert.convert_with_fallback ~from_codeset:"UTF-8" ~to_codeset:char_set s)
    end else 	
      (prerr_endline ("Manual charset is "^ !current.encoding_manual);
       Glib.Convert.convert_with_fallback ~from_codeset:"UTF-8" ~to_codeset:!current.encoding_manual s)
    with e -> (prerr_endline ("Error ("^(Printexc.to_string e)^") in transcoding: falling back to UTF-8") ;s)
  in
  let oc = open_out file_name in
  output_string oc s;
  close_out oc;
  true
  with e -> prerr_endline (Printexc.to_string e);false

let my_stat f = try Some (Unix.stat f) with _ -> None

let revert_timer = ref None
let disconnect_revert_timer () = match !revert_timer with
  | None -> ()
  | Some id -> GMain.Timeout.remove id; revert_timer := None

let auto_save_timer = ref None
let disconnect_auto_save_timer () = match !auto_save_timer with
  | None -> ()
  | Some id -> GMain.Timeout.remove id; auto_save_timer := None

let highlight_timer = ref None
let set_highlight_timer f = 
  match !highlight_timer with 
    | None -> 
	revert_timer := 
      Some (GMain.Timeout.add ~ms:2000 
	      ~callback:(fun () -> f (); highlight_timer := None; true))
    | Some id -> 
	GMain.Timeout.remove id;
	revert_timer := 
	Some (GMain.Timeout.add ~ms:2000 
		~callback:(fun () -> f (); highlight_timer := None; true))


(* Get back the standard coq out channels *)
let init_stdout,read_stdout,clear_stdout =
  let out_buff = Buffer.create 100 in
  let out_ft = Format.formatter_of_buffer out_buff in
  let deep_out_ft = Format.formatter_of_buffer out_buff in
  let _ = Pp_control.set_gp deep_out_ft Pp_control.deep_gp in
  (fun () -> 
    Pp_control.std_ft := out_ft;
    Pp_control.err_ft := out_ft;
    Pp_control.deep_ft := deep_out_ft;
),
  (fun () -> Format.pp_print_flush out_ft (); 
     let r = Buffer.contents out_buff in
     prerr_endline "Output from Coq is: "; prerr_endline r;
     Buffer.clear out_buff; r),
  (fun () -> 
     Format.pp_print_flush out_ft (); Buffer.clear out_buff)


let last_dir = ref ""

let filter_all_files () = GFile.filter 
  ~name:"All" 
  ~patterns:["*"] () 
  
let filter_coq_files () =  GFile.filter 
  ~name:"Coq source code" 
  ~patterns:[ "*.v"] ()

let select_file_for_open ~title ?(dir = last_dir) ?(filename="") () =
  let file = ref None in 
  let file_chooser = GWindow.file_chooser_dialog ~action:`OPEN ~modal:true ~title () in
    file_chooser#add_button_stock `CANCEL `CANCEL ;
    file_chooser#add_select_button_stock `OPEN `OPEN ;
    file_chooser#add_filter (filter_coq_files ());
    file_chooser#add_filter (filter_all_files ());
    ignore (file_chooser#set_current_folder !dir);
    begin match file_chooser#run () with
      | `OPEN -> 
	  begin 
	    file := file_chooser#filename;
	    match !file with
		None -> ()
	      | Some s -> dir := Filename.dirname s;
	  end
      | `DELETE_EVENT | `CANCEL -> ()
    end ;
    file_chooser#destroy ();	    
    !file


let select_file_for_save ~title ?(dir = last_dir) ?(filename="") () =
  let file = ref None in 
  let file_chooser = GWindow.file_chooser_dialog ~action:`SAVE ~modal:true ~title () in
    file_chooser#add_button_stock `CANCEL `CANCEL ;
    file_chooser#add_select_button_stock `SAVE `SAVE ;
    file_chooser#add_filter (filter_coq_files ());
    file_chooser#add_filter (filter_all_files ());
  (* this line will be used when a lablgtk >= 2.10.0 is the default on most distributions  
       file_chooser#set_do_overwrite_confirmation true;
     *)
    ignore (file_chooser#set_current_folder !dir);
    ignore (file_chooser#set_current_name filename);
    
    begin match file_chooser#run () with
      | `SAVE -> 
	  begin 
	    file := file_chooser#filename;
	    match !file with
		None -> ()
	      | Some s -> dir := Filename.dirname s;
	  end
      | `DELETE_EVENT | `CANCEL -> ()
    end ;
    file_chooser#destroy ();	    
    !file

let find_tag_start (tag :GText.tag) (it:GText.iter) =
  let it = it#copy in
  let tag = Some tag in
  while not (it#begins_tag tag) && it#nocopy#backward_char do
    ()
  done;
  it
let find_tag_stop (tag :GText.tag) (it:GText.iter) =
  let it = it#copy in
  let tag = Some tag in
  while not (it#ends_tag tag) && it#nocopy#forward_char do
    ()
  done;
  it
let find_tag_limits (tag :GText.tag) (it:GText.iter) = 
 (find_tag_start tag it , find_tag_stop tag it)

(* explanations: Win32 threads won't work if events are produced
   in a thread different from the thread of the Gtk loop. In this
   case we must use GtkThread.async to push a callback in the
   main thread. Beware that the synchronus version may produce
   deadlocks. *)
let async = 
  if Sys.os_type = "Win32" then GtkThread.async else (fun x -> x)
let sync = 
  if Sys.os_type = "Win32" then GtkThread.sync else (fun x -> x)

let mutex text f =
  let m = Mutex.create() in
  fun x ->
    if Mutex.try_lock m
    then 
      (try
        prerr_endline ("Got lock on "^text);
        f x;
        Mutex.unlock m;
        prerr_endline ("Released lock on "^text)
      with e ->
        Mutex.unlock m;
        prerr_endline ("Released lock on "^text^" (on error)");
        raise e)
    else
      prerr_endline
        ("Discarded call for "^text^": computations ongoing")


let stock_to_widget ?(size=`DIALOG) s = 
  let img = GMisc.image () 
  in img#set_stock s;
  img#coerce

let rec print_list print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; print_list print fmt r

(* TODO: allow to report output as soon as it comes (user-fiendlier
   for long commands like make...) *)
let run_command f c =
  let result = Buffer.create 127 in
  let cin,cout,cerr = Unix.open_process_full c (Unix.environment ()) in
  let buff = String.make 127 ' ' in
  let buffe = String.make 127 ' ' in
  let n = ref 0 in
  let ne = ref 0 in
  while n:= input cin buff 0 127 ; ne := input cerr buffe 0 127 ; !n+ !ne <> 0
  do
    let r = try_convert (String.sub buff 0 !n) in 
    f r;
    Buffer.add_string result r;
    let r = try_convert (String.sub buffe 0 !ne) in 
    f r;
    Buffer.add_string result r 
  done;
  (Unix.close_process_full (cin,cout,cerr),  Buffer.contents result)

let browse f url =
  let com = Flags.subst_command_placeholder !current.cmd_browse url in
  let s = Sys.command com in
  if s = 127 then
    f ("Could not execute\n\""^com^
       "\"\ncheck your preferences for setting a valid browser command\n")

let url_for_keyword =
  let ht = Hashtbl.create 97 in
  begin try
    let cin = open_in (lib_ide_file "index_urls.txt") in
    try while true do
      let s = input_line cin in
      try 
	let i = String.index s ',' in
	let k = String.sub s 0 i in
	let u = String.sub s (i + 1) (String.length s - i - 1) in
	Hashtbl.add ht k u
      with _ ->
	()
    done with End_of_file ->
      close_in cin
  with _ ->
    ()
  end;
  (Hashtbl.find ht : string -> string)


let browse_keyword f text = 
  try let u = url_for_keyword text in browse f (!current.doc_url ^ u) 
  with Not_found -> f ("No documentation found for "^text)


let underscore = Glib.Utf8.to_unichar "_" (ref 0)

let arobase = Glib.Utf8.to_unichar "@" (ref 0)
let prime = Glib.Utf8.to_unichar "'" (ref 0)
let bn = Glib.Utf8.to_unichar "\n" (ref 0)
let space = Glib.Utf8.to_unichar " " (ref 0)
let tab = Glib.Utf8.to_unichar "\t" (ref 0)


(*
  checks if two file names refer to the same (existing) file by
  comparing their device and inode. 
  It seems that under Windows, inode is always 0, so we cannot
  accurately check if 

*)
(* Optimised for partial application (in case many candidates must be
   compared to f1). *)
let same_file f1 =
  try
    let s1 = Unix.stat f1 in
    (fun f2 ->
      try
        let s2 = Unix.stat f2 in
        s1.Unix.st_dev = s2.Unix.st_dev &&
          if Sys.os_type = "Win32" then f1 = f2 
          else s1.Unix.st_ino = s2.Unix.st_ino
      with
          Unix.Unix_error _ -> false)
  with
      Unix.Unix_error _ -> (fun _ -> false)

let absolute_filename f =
  if Filename.is_relative f then 
    Filename.concat (Sys.getcwd ()) f
  else f
	      
