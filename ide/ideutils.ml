(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)


open Preferences

exception Forbidden

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
	 prerr_endline 
	   ("Coqide warning: trying to convert from locale ("^char_set^")");
	 Glib.Convert.convert_with_fallback ~to_codeset:"UTF-8" ~from_codeset:char_set s
       in
       let from_manual () = 
	 prerr_endline 
	   ("Coqide warning: trying to convert from "^ !current.encoding_manual);
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

let browse url =
  let l,r = !current.cmd_browse in
  ignore (Sys.command (l ^ url ^ r))

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


let browse_keyword text = 
  try let u = url_for_keyword text in browse (!current.doc_url ^ u) 
  with _ -> ()

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
        GWindow.file_selection ~fileop_buttons:true ~modal:true ~title ~filename ()
      else
        GWindow.file_selection ~fileop_buttons:true ~modal:true ~title ()
    end else begin
      dir := Filename.dirname filename;
      GWindow.file_selection ~fileop_buttons:true ~modal:true ~title ~filename ()
    end
  in
  fs#complete ~filter:"";
  ignore (fs#connect#destroy ~callback: GMain.Main.quit);
  let file = ref None in 
  ignore (fs#ok_button#connect#clicked ~callback:
    begin fun () ->
      file := Some fs#get_filename; 
      dir := Filename.dirname fs#get_filename;
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

let async = 
  if Sys.os_type <> "Unix" then GtkThread.async else (fun x -> x)


let stock_to_widget ?(size=`DIALOG) s = 
  let img = GMisc.image () 
  in img#set_stock ~size s ;
  img#coerce

let rec print_list print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; print_list print fmt r


let run_command f c =
  let result = Buffer.create 127 in
  let cin,cout,cerr = Unix.open_process_full c (Unix.environment ()) in
  let buff = String.make 127 ' ' in
  let buffe = String.make 127 ' ' in
  let n = ref 0 in
  let ne = ref 0 in

  while n:= input cin buff 0 127 ; ne := input cerr buffe 0 127 ; 
    !n+ !ne <> 0
  do 
    let r = try_convert (String.sub buff 0 !n) in 
    f r;
    Buffer.add_string result r;
    let r = try_convert (String.sub buffe 0 !ne) in 
    f r;
    Buffer.add_string result r 
  done;
  (Unix.close_process_full (cin,cout,cerr),  Buffer.contents result)

let underscore = Glib.Utf8.to_unichar "_" (ref 0)
let bn = Glib.Utf8.to_unichar "\n" (ref 0)
let space = Glib.Utf8.to_unichar " " (ref 0)
let tab = Glib.Utf8.to_unichar "\t" (ref 0)
