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


let debug = Options.debug

let prerr_endline s =
  if !debug then (prerr_endline s;flush stderr)
let prerr_string s =
  if !debug then (prerr_string s;flush stderr)

let lib_ide = Filename.concat Coq_config.coqlib "ide"
  
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

let process_pending () =
  prerr_endline "Pending process";()
(*  try 
    while Glib.Main.pending () do 
      ignore (Glib.Main.iteration false)
    done
  with e -> 
    prerr_endline "Pending problems : expect a crash very soon";
    raise e
*)

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
let read_stdout,clear_stdout =
  let out_buff = Buffer.create 100 in
  Pp_control.std_ft := Format.formatter_of_buffer out_buff;
  (fun () -> Format.pp_print_flush !Pp_control.std_ft (); 
     let r = Buffer.contents out_buff in
     Buffer.clear out_buff; r),
  (fun () -> 
     Format.pp_print_flush !Pp_control.std_ft (); Buffer.clear out_buff)


let last_dir = ref ""
let select_file ~title ?(dir = last_dir) ?(filename="") () =
  let fs =
    if Filename.is_relative filename then begin
      if !dir <> "" then
        let filename = Filename.concat !dir filename in 
        GWindow.file_selection ~show_fileops:true ~modal:true ~title ~filename ()
      else
        GWindow.file_selection ~show_fileops:true ~modal:true ~title ()
    end else begin
      dir := Filename.dirname filename;
      GWindow.file_selection ~show_fileops:true ~modal:true ~title ~filename ()
    end
  in
  fs#complete ~filter:"";
  ignore (fs#connect#destroy ~callback: GMain.Main.quit);
  let file = ref None in 
  ignore (fs#ok_button#connect#clicked ~callback:
    begin fun () ->
      file := Some fs#filename; 
      dir := Filename.dirname fs#filename;
      fs#destroy ()
    end);
  ignore (fs # cancel_button # connect#clicked ~callback:fs#destroy);
  fs # show ();
  GMain.Main.main ();
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

(* explanations ?? *)
let async = 
  if Sys.os_type <> "Unix" then GtkThread.async else 
    (fun x -> x)

let stock_to_widget ?(size=`DIALOG) s = 
  let img = GMisc.image () 
  in img#set_stock s;
  img#coerce

let rec print_list print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; print_list print fmt r


let browse f url =
  let l,r = !current.cmd_browse in
  let _ = System.run_command try_convert f (l ^ url ^ r) in
  ()

let url_for_keyword =
  let ht = Hashtbl.create 97 in
  begin try
    let cin = open_in (Filename.concat lib_ide "index_urls.txt") in
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
  with _ -> ()


let underscore = Glib.Utf8.to_unichar "_" (ref 0)

let arobase = Glib.Utf8.to_unichar "@" (ref 0)
let prime = Glib.Utf8.to_unichar "'" (ref 0)
let bn = Glib.Utf8.to_unichar "\n" (ref 0)
let space = Glib.Utf8.to_unichar " " (ref 0)
let tab = Glib.Utf8.to_unichar "\t" (ref 0)


(*
  checks if two file names refer to the same (existing) file
*)

let same_file f1 f2 =
  try
    let s1 = Unix.stat f1
    and s2 = Unix.stat f2 
    in
    (s1.Unix.st_dev = s2.Unix.st_dev) &&
    (s1.Unix.st_ino = s2.Unix.st_ino) 
  with
      Unix.Unix_error _ -> false

let absolute_filename f =
  if Filename.is_relative f then 
    Filename.concat (Sys.getcwd ()) f
  else f
	      
