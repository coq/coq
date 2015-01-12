(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


open Preferences

exception Forbidden

let warn_image () =
  let img = GMisc.image () in
  img#set_stock `DIALOG_WARNING;
  img#set_icon_size `DIALOG;
  img

let warning msg = 
   GToolbox.message_box ~title:"Warning" ~icon:(warn_image ())#coerce msg 

let cb = GData.clipboard Gdk.Atom.primary

(* status bar and locations *)

let status = GMisc.statusbar ()

let push_info,pop_info,clear_info =
  let status_context = status#new_context ~name:"Messages" in
  let size = ref 0 in
  (fun s -> incr size; ignore (status_context#push s)),
  (fun () -> decr size; status_context#pop ()),
  (fun () -> for i = 1 to !size do status_context#pop () done; size := 0)

let flash_info =
  let flash_context = status#new_context ~name:"Flash" in
    (fun ?(delay=5000) s -> flash_context#flash ~delay s)



let set_location = ref  (function s -> failwith "not ready")

(** A utf8 char is either a single byte (ascii char, 0xxxxxxx)
    or multi-byte (with a leading byte 11xxxxxx and extra bytes 10xxxxxx) *)

let is_extra_byte c = ((Char.code c) lsr 6 = 2)

(** For a string buffer that may contain utf8 chars,
    we convert a byte offset into a char offset
    by only counting char-starting bytes.
    Normally the string buffer starts with a char-starting byte
    (buffer produced by a [#get_text]) *)

let byte_offset_to_char_offset s byte_offset =
  let extra_bytes = ref 0 in
  for i = 0 to min byte_offset (String.length s - 1) do
    if is_extra_byte s.[i] then incr extra_bytes
  done;
  byte_offset - !extra_bytes

let glib_utf8_pos_to_offset s ~off = byte_offset_to_char_offset s off

let do_convert s =
  let from_loc () =
    let _,char_set = Glib.Convert.get_charset () in
    flash_info ("Converting from locale ("^char_set^")");
    Glib.Convert.convert_with_fallback
      ~to_codeset:"UTF-8" ~from_codeset:char_set s
  in
  let from_manual enc =
    flash_info ("Converting from "^ enc);
    Glib.Convert.convert s ~to_codeset:"UTF-8" ~from_codeset:enc
  in
  let s =
    if Glib.Utf8.validate s then (Minilib.log "Input is UTF-8"; s)
    else match current.encoding with
      |Preferences.Eutf8 | Preferences.Elocale -> from_loc ()
      |Emanual enc -> try from_manual enc with _ -> from_loc ()
  in
  Utf8_convert.f s

let try_convert s =
  try
    do_convert s
  with _ ->
    "(* Fatal error: wrong encoding in input. \
Please choose a correct encoding in the preference panel.*)";;


let try_export file_name s =
  let s =
    try match current.encoding with
      |Eutf8 -> Minilib.log "UTF-8 is enforced" ; s
      |Elocale ->
	let is_unicode,char_set = Glib.Convert.get_charset () in
	if is_unicode then
	  (Minilib.log "Locale is UTF-8" ; s)
	else
	  (Minilib.log ("Locale is "^char_set);
	   Glib.Convert.convert_with_fallback
             ~from_codeset:"UTF-8" ~to_codeset:char_set s)
      |Emanual enc ->
	(Minilib.log ("Manual charset is "^ enc);
         Glib.Convert.convert_with_fallback
           ~from_codeset:"UTF-8" ~to_codeset:enc s)
    with e ->
      let str = Printexc.to_string e in
      Minilib.log ("Error ("^str^") in transcoding: falling back to UTF-8");
      s
  in
  try
    let oc = open_out file_name in
    output_string oc s;
    close_out oc;
    true
  with e -> Minilib.log (Printexc.to_string e);false

type timer = { run : ms:int -> callback:(unit->bool) -> unit;
               kill : unit -> unit }

let mktimer () =
  let timer = ref None in
  { run =
      (fun ~ms ~callback ->
          timer := Some (GMain.Timeout.add ~ms ~callback));
    kill =
      (fun () -> match !timer with
        | None -> ()
        | Some id ->
            (try GMain.Timeout.remove id
             with Glib.GError _ -> ());
             timer := None) }

let last_dir = ref ""

let filter_all_files () = GFile.filter
  ~name:"All"
  ~patterns:["*"] ()

let filter_coq_files () =  GFile.filter
  ~name:"Coq source code"
  ~patterns:[ "*.v"] ()

let select_file_for_open ~title () =
  let file = ref None in
  let file_chooser =
    GWindow.file_chooser_dialog ~action:`OPEN ~modal:true ~title ()
  in
  file_chooser#add_button_stock `CANCEL `CANCEL ;
  file_chooser#add_select_button_stock `OPEN `OPEN ;
  file_chooser#add_filter (filter_coq_files ());
  file_chooser#add_filter (filter_all_files ());
  file_chooser#set_default_response `OPEN;
  ignore (file_chooser#set_current_folder !last_dir);
  begin match file_chooser#run () with
    | `OPEN ->
      begin
	file := file_chooser#filename;
	match !file with
	  | None -> ()
	  | Some s -> last_dir := Filename.dirname s;
      end
    | `DELETE_EVENT | `CANCEL -> ()
  end ;
  file_chooser#destroy ();
  !file

let select_file_for_save ~title ?filename () =
  let file = ref None in
  let file_chooser =
    GWindow.file_chooser_dialog ~action:`SAVE ~modal:true ~title ()
  in
  file_chooser#add_button_stock `CANCEL `CANCEL ;
  file_chooser#add_select_button_stock `SAVE `SAVE ;
  file_chooser#add_filter (filter_coq_files ());
  file_chooser#add_filter (filter_all_files ());
  (* this line will be used when a lablgtk >= 2.10.0 is the default
     on most distributions:
     file_chooser#set_do_overwrite_confirmation true;
  *)
  file_chooser#set_default_response `SAVE;
  let dir,filename = match filename with
    |None -> !last_dir, ""
    |Some f -> Filename.dirname f, Filename.basename f
  in
  ignore (file_chooser#set_current_folder dir);
  ignore (file_chooser#set_current_name filename);
  begin match file_chooser#run () with
    | `SAVE ->
      begin
        file := file_chooser#filename;
        match !file with
            None -> ()
          | Some s -> last_dir := Filename.dirname s;
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

let stock_to_widget ?(size=`BUTTON) s =
  let img = GMisc.image () in
  (match size with
    | `CUSTOM(width,height) ->
         let opb = img#misc#render_icon ~size:`BUTTON s in
         let pb = GdkPixbuf.create ~width ~height
           ~bits:(GdkPixbuf.get_bits_per_sample opb)
           ~has_alpha:(GdkPixbuf.get_has_alpha opb) () in
         GdkPixbuf.scale ~width ~height ~dest:pb opb;
         img#set_pixbuf pb
    | #Gtk.Tags.icon_size as icon_size ->
         img#set_stock s;
         img#set_icon_size icon_size);
  img#coerce

let custom_coqtop = ref None

let coqtop_path () =
  let file = match !custom_coqtop with
    | Some s -> s
    | None ->
      match current.cmd_coqtop with
	| Some s -> s
	| None ->
	  let prog = String.copy Sys.executable_name in
	  try
	    let pos = String.length prog - 6 in
	    let i = Str.search_backward (Str.regexp_string "coqide") prog pos
            in
	    String.blit "coqtop" 0 prog i 6;
	    if Sys.file_exists prog then prog else "coqtop"
	  with Not_found -> "coqtop"
  in file

(* In win32, when a command-line is to be executed via cmd.exe
   (i.e. Sys.command, Unix.open_process, ...), it cannot contain several
   quoted "..." zones otherwise some quotes are lost. Solution: we re-quote
   everything. Reference: http://ss64.com/nt/cmd.html *)

let requote cmd = if Sys.os_type = "Win32" then "\""^cmd^"\"" else cmd

let textview_width (view : #GText.view_skel) =
  let rect = view#visible_rect in
  let pixel_width = Gdk.Rectangle.width rect in
  let metrics = view#misc#pango_context#get_metrics ()  in
  let char_width = GPango.to_pixels metrics#approx_char_width in
  pixel_width / char_width

type logger = Pp.message_level -> string -> unit

let default_logger level message =
  let level = match level with
  | Pp.Debug _ -> `DEBUG
  | Pp.Info -> `INFO
  | Pp.Notice -> `NOTICE
  | Pp.Warning -> `WARNING
  | Pp.Error -> `ERROR
  in
  Minilib.log ~level message


(** {6 File operations} *)

(** A customized [stat] function. Exceptions are catched. *)

type stats = MTime of float | NoSuchFile | OtherError

let stat f =
  try MTime (Unix.stat f).Unix.st_mtime
  with
    | Unix.Unix_error (Unix.ENOENT,_,_) -> NoSuchFile
    | _ -> OtherError

(** I/O utilities

    Note: In a mono-thread coqide, we use the same buffer for
    different read operations *)

let maxread = 4096

let read_string = String.create maxread
let read_buffer = Buffer.create maxread

(** Read the content of file [f] and add it to buffer [b].
    I/O Exceptions are propagated. *)

let read_file name buf =
  let ic = open_in name in
  let len = ref 0 in
  try
    while len := input ic read_string 0 maxread; !len > 0 do
      Buffer.add_substring buf read_string 0 !len
    done;
    close_in ic
  with e -> close_in ic; raise e

(** Read what is available on a gtk channel. This channel should have been
    set as non-blocking. When there's nothing more to read, the inner loop
    will be exited via a GError exception concerning a EAGAIN unix error.
    Anyway, any other exception also stops the read. *)

let io_read_all chan =
  Buffer.clear read_buffer;
  let read_once () =
    let len = Glib.Io.read_chars ~buf:read_string ~pos:0 ~len:maxread chan in
    Buffer.add_substring read_buffer read_string 0 len
  in
  begin
    try while true do read_once () done
    with Glib.GError _ -> ()
  end;
  Buffer.contents read_buffer

(** Run an external command asynchronously *)

let run_command display finally cmd =
  let cin = Unix.open_process_in cmd in
  let fd = Unix.descr_of_in_channel cin in
  let () = Unix.set_nonblock fd in
  let io_chan = Glib.Io.channel_of_descr fd in
  let all_conds = [`ERR; `HUP; `IN; `NVAL; `PRI] in (* all except `OUT *)
  let rec has_errors = function
    | [] -> false
    | (`IN | `PRI) :: conds -> has_errors conds
    | e :: _ -> true
  in
  let handle_end () = finally (Unix.close_process_in cin); false
  in
  let handle_input conds =
    if has_errors conds then handle_end ()
    else
      let s = io_read_all io_chan in
      if s = "" then handle_end ()
      else (display (try_convert s); true)
  in
  ignore (Glib.Io.add_watch ~cond:all_conds ~callback:handle_input io_chan)

(** Web browsing *)

let browse prerr url =
  let com = Util.subst_command_placeholder current.cmd_browse url in
  let finally = function
    | Unix.WEXITED 127 ->
      prerr
        ("Could not execute:\n"^com^"\n"^
         "check your preferences for setting a valid browser command\n")
    | _ -> ()
  in
  run_command (fun _ -> ()) finally com

let doc_url () =
  if current.doc_url = use_default_doc_url || current.doc_url = ""
  then
    let addr = List.fold_left Filename.concat (Coq_config.docdir)
      ["html";"refman";"index.html"]
    in
    if Sys.file_exists addr then "file://"^addr else Coq_config.wwwrefman
  else current.doc_url

let url_for_keyword =
  let ht = Hashtbl.create 97 in
    lazy (
      begin try
        let cin =
          try let index_urls = Filename.concat (List.find
            (fun x -> Sys.file_exists (Filename.concat x "index_urls.txt"))
            (Minilib.coqide_data_dirs ())) "index_urls.txt" in
            open_in index_urls
          with Not_found ->
            let doc_url = doc_url () in
            let n = String.length doc_url in
              if n > 8 && String.sub doc_url 0 7 = "file://" then
                open_in (String.sub doc_url 7 (n-7) ^ "index_urls.txt")
              else
                raise Exit
        in
          try while true do
            let s = input_line cin in
              try
                let i = String.index s ',' in
                let k = String.sub s 0 i in
                let u = String.sub s (i + 1) (String.length s - i - 1) in
                  Hashtbl.add ht k u
              with _ ->
                Minilib.log "Warning: Cannot parse documentation index file."
          done with End_of_file ->
            close_in cin
      with _ ->
        Minilib.log "Warning: Cannot find documentation index file."
      end;
      Hashtbl.find ht : string -> string)

let browse_keyword prerr text =
  try
    let u = Lazy.force url_for_keyword text in
    browse prerr (doc_url() ^ u)
  with Not_found -> prerr ("No documentation found for \""^text^"\".\n")

