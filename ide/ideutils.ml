(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


open Preferences

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
  (fun () -> for _i = 1 to !size do status_context#pop () done; size := 0)

let flash_info =
  let flash_context = status#new_context ~name:"Flash" in
    (fun ?(delay=5000) s -> flash_context#flash ~delay s)

(* Note: Setting the same attribute with two separate tags appears to use
the first value applied and not the second.  I saw this trying to set the background
color on Windows.  A clean fix, if ever needed, would be to combine the attributes
of the tags into a single composite tag before applying.  This is left as an
exercise for the reader. *)
let insert_with_tags (buf : #GText.buffer_skel) mark rmark tags text =
  (** FIXME: LablGTK2 does not export the C insert_with_tags function, so that
      it has to reimplement its own helper function. Unluckily, it relies on
      a slow algorithm, so that we have to have our own quicker version here.
      Alas, it is still much slower than the native version... *)
  if CList.is_empty tags then buf#insert ~iter:(buf#get_iter_at_mark mark) text
  else
    let it = buf#get_iter_at_mark mark in
    let () = buf#move_mark rmark ~where:it in
    let () = buf#insert ~iter:(buf#get_iter_at_mark mark) text in
    let start = buf#get_iter_at_mark mark in
    let stop = buf#get_iter_at_mark rmark in
    let iter tag = buf#apply_tag tag ~start ~stop in
    List.iter iter (List.rev tags)

let nl_white_regex = Str.regexp "^\\( *\n *\\)"
let diff_regex = Str.regexp "^diff."

let insert_xml ?(mark = `INSERT) ?(tags = []) (buf : #GText.buffer_skel) msg =
  let open Xml_datatype in
  let dtags = ref [] in
  let tag name =
    match GtkText.TagTable.lookup buf#tag_table name with
    | None -> raise Not_found
    | Some tag -> new GText.tag tag
  in
  let rmark = `MARK (buf#create_mark buf#start_iter) in
  (* insert the string, but don't apply diff highlights to white space at the begin/end of line *)
  let rec insert_str tags s =
    let etags = try List.hd !dtags :: tags with hd -> tags in
    try
      let start = Str.search_forward nl_white_regex s 0 in
      insert_with_tags buf mark rmark etags (String.sub s 0 start);
      insert_with_tags buf mark rmark tags (Str.matched_group 1 s);
      let mend = Str.match_end () in
      insert_str tags (String.sub s mend (String.length s - mend))
    with Not_found ->
      insert_with_tags buf mark rmark etags s
  in
  let rec insert tags = function
  | PCData s -> insert_str tags s
  | Element (t, _, children) ->
    let (pfx, tname) = Pp.split_tag t in
    let is_diff = try let _ = Str.search_forward diff_regex tname 0 in true with Not_found -> false in
    let (tags, have_tag) =
      try
        let t = tag tname in
        if is_diff && pfx <> Pp.end_pfx then
          dtags := t :: !dtags;
        if pfx = "" then
          ((if is_diff then tags else t :: tags), true)
        else
          (tags, true)
      with Not_found -> (tags, false)
    in
    List.iter (fun xml -> insert tags xml) children;
    if have_tag && is_diff && pfx <> Pp.start_pfx then
      dtags := (try List.tl !dtags with tl -> []);
  in
  let () = try insert tags msg with _ -> () in
  buf#delete_mark rmark

let set_location = ref  (function s -> failwith "not ready")

let display_location ins =
  let line = ins#line + 1 in
  let off = ins#line_offset + 1 in
  let msg = Printf.sprintf "Line: %5d Char: %3d" line off in
  !set_location msg

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
    else match encoding#get with
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

let export file_name s =
  let oc = open_out_bin file_name in
  let ending = line_ending#get in
  let is_windows = ref false in
  for i = 0 to String.length s - 1 do
    match s.[i] with
    | '\r' -> is_windows := true
    | '\n' ->
      begin match ending with
      | `DEFAULT ->
        if !is_windows then (output_char oc '\r'; output_char oc '\n')
        else output_char oc '\n'
      | `WINDOWS -> output_char oc '\r'; output_char oc '\n'
      | `UNIX -> output_char oc '\n'
      end
    | c -> output_char oc c
  done;
  close_out oc

let try_export file_name s =
  let s =
    try match encoding#get with
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
  try export file_name s; true
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

let filter_all_files () = GFile.filter
  ~name:"All"
  ~patterns:["*"] ()

let filter_coq_files () =  GFile.filter
  ~name:"Coq source code"
  ~patterns:[ "*.v"] ()

let current_dir () = match project_path#get with
| None -> ""
| Some dir -> dir

let select_file_for_open ~title ?filename () =
  let file_chooser =
    GWindow.file_chooser_dialog ~action:`OPEN ~modal:true ~title ()
  in
  file_chooser#add_button_stock `CANCEL `CANCEL ;
  file_chooser#add_select_button_stock `OPEN `OPEN ;
  file_chooser#add_filter (filter_coq_files ());
  file_chooser#add_filter (filter_all_files ());
  file_chooser#set_default_response `OPEN;
  let dir = match filename with
    | None -> current_dir ()
    | Some f -> Filename.dirname f in
  ignore (file_chooser#set_current_folder dir);
  let file =
    match file_chooser#run () with
    | `OPEN ->
      begin
	match file_chooser#filename with
	  | None -> None
	  | Some _ as f ->
            project_path#set file_chooser#current_folder; f
      end
    | `DELETE_EVENT | `CANCEL -> None in
  file_chooser#destroy ();
  file

let select_file_for_save ~title ?filename () =
  let file = ref None in
  let file_chooser =
    GWindow.file_chooser_dialog ~action:`SAVE ~modal:true ~title ()
  in
  file_chooser#add_button_stock `CANCEL `CANCEL ;
  file_chooser#add_select_button_stock `SAVE `SAVE ;
  file_chooser#add_filter (filter_coq_files ());
  file_chooser#add_filter (filter_all_files ());
  file_chooser#set_do_overwrite_confirmation true;
  file_chooser#set_default_response `SAVE;
  let dir,filename = match filename with
    |None -> current_dir (), ""
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
          | Some s -> project_path#set file_chooser#current_folder
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
      match cmd_coqtop#get with
      | Some s -> s
      | None ->
        try
          let new_prog = System.get_toplevel_path "coqidetop" in
            if Sys.file_exists new_prog then new_prog
	    else
	      let in_macos_bundle =
		Filename.concat
		  (Filename.dirname new_prog)
		  (Filename.concat "../Resources/bin" (Filename.basename new_prog))
	      in if Sys.file_exists in_macos_bundle then in_macos_bundle
                 else "coqidetop"
        with Not_found -> "coqidetop"
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

type logger = Feedback.level -> Pp.t -> unit

let default_logger level message =
  let level = match level with
  | Feedback.Debug -> `DEBUG
  | Feedback.Info -> `INFO
  | Feedback.Notice -> `NOTICE
  | Feedback.Warning -> `WARNING
  | Feedback.Error -> `ERROR
  in
  Minilib.log_pp ~level message


(** {6 File operations} *)

(** A customized [stat] function. Exceptions are caught. *)

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

let read_string = Bytes.create maxread
let read_buffer = Buffer.create maxread

(** Read the content of file [f] and add it to buffer [b].
    I/O Exceptions are propagated. *)

let read_file name buf =
  let ic = Util.open_utf8_file_in name in
  let len = ref 0 in
  try
    while len := input ic read_string 0 maxread; !len > 0 do
      Buffer.add_subbytes buf read_string 0 !len
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
    Buffer.add_subbytes read_buffer read_string 0 len
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
  let com = Util.subst_command_placeholder cmd_browse#get url in
  let finally = function
    | Unix.WEXITED 127 ->
      prerr
        ("Could not execute:\n"^com^"\n"^
         "check your preferences for setting a valid browser command\n")
    | _ -> ()
  in
  run_command (fun _ -> ()) finally com

let doc_url () =
  if doc_url#get = use_default_doc_url || doc_url#get = ""
  then
    let addr = List.fold_left Filename.concat (Envars.docdir ())
      ["html";"refman";"index.html"]
    in
    if Sys.file_exists addr then "file://"^addr else Coq_config.wwwrefman
  else doc_url#get

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

let rec is_valid (s : Pp.t) = match Pp.repr s with
  | Pp.Ppcmd_empty
  | Pp.Ppcmd_print_break _
  | Pp.Ppcmd_force_newline  -> true
  | Pp.Ppcmd_glue l    -> List.for_all is_valid l
  | Pp.Ppcmd_string s  -> Glib.Utf8.validate s
  | Pp.Ppcmd_box (_,s)
  | Pp.Ppcmd_tag (_,s) -> is_valid s
  | Pp.Ppcmd_comment s -> List.for_all Glib.Utf8.validate s
let validate s =
  if is_valid s then s else Pp.str "This error massage can't be printed."
