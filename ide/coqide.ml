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
open Gtk_parsing
open Ideutils
open Session

(** Note concerning GtkTextBuffer

    Be careful with gtk calls on text buffers, since many are non-atomic :
    they emit a gtk signal and the handlers for this signal are run
    immediately, before returning to the current function.
    Here's a partial list of these signals and the methods that
    trigger them (cf. documentation of GtkTextBuffer, signal section)

      begin_user_action : #begin_user_action, #insert_interactive,
        #insert_range_interactive, #delete_interactive, #delete_selection
      end_user_action : #end_user_action, #insert_interactive,
        #insert_range_interactive, #delete_interactive, #delete_selection

      insert_text : #insert (and variants)
      delete_range : #delete (and variants)

      apply_tag : #apply_tag, (and some #insert)
      remove_tag : #remove_tag

      mark_deleted : #delete_mark
      mark_set : #create_mark, #move_mark

      changed : ... (whenever a buffer has changed)
      modified_changed : #set_modified (and whenever the modified bit flips)

   Caveat : when the buffer is modified, all iterators on it become
   invalid and shouldn't be used (nasty errors otherwise). There are
   some special cases : boundaries given to #insert and #delete are
   revalidated by the default signal handler.
*)

(** {2 Some static elements } *)

(** The arguments that will be passed to coqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
let custom_project_file = ref None
let sup_args = ref []

let logfile = ref None

(** {2 Notebook of sessions } *)

(** The main element of coqide is a notebook of session views *)

let notebook =
  Wg_Notebook.create Session.build_layout Session.kill
    ~border_width:2 ~show_border:false ~scrollable:true ()


(** {2 Callback functions for the user interface } *)

let on_current_term f =
  let term = try Some notebook#current_term with Invalid_argument _ -> None in
  match term with
  | None -> ()
  | Some t -> ignore (f t)

let cb_on_current_term f _ = on_current_term f

(** Nota: using && here has the advantage of working both under win32 and unix.
    If someday we want the main command to be tried even if the "cd" has failed,
    then we should use " ; " under unix but " & " under win32 (cf. #2363). *)

let local_cd file =
  "cd " ^ Filename.quote (Filename.dirname file) ^ " && "

let pr_exit_status = function
  | Unix.WEXITED 0 -> " succeeded"
  | _ -> " failed"

let make_coqtop_args fname =
  let open CoqProject_file in
  let base_args = match read_project#get with
    | Ignore_args -> !sup_args
    | Append_args -> !sup_args
    | Subst_args -> [] in
  if read_project#get = Ignore_args then "", base_args
  else
    match !custom_project_file, fname with
    | Some (d,proj), _ -> d, coqtop_args_from_project proj @ base_args
    | None, None -> "", base_args
    | None, Some the_file ->
       match
         CoqProject_file.find_project_file
           ~from:(Filename.dirname the_file)
           ~projfile_name:project_file_name#get
       with
       | None -> "", base_args
       | Some proj -> 
           proj, coqtop_args_from_project (read_project_file proj) @ base_args
;;

(** Setting drag & drop on widgets *)

let load_file_cb : (string -> unit) ref = ref ignore

let drop_received context ~x ~y data ~info ~time =
  if data#format = 8 then begin
    let files = Str.split (Str.regexp "\r?\n") data#data in
    let path = Str.regexp "^file://\\(.*\\)$" in
    List.iter (fun f ->
      if Str.string_match path f 0 then
        !load_file_cb (Str.matched_group 1 f)
    ) files;
    context#finish ~success:true ~del:false ~time
  end else context#finish ~success:false ~del:false ~time

let drop_targets = [
  { Gtk.target = "text/uri-list"; Gtk.flags = []; Gtk.info = 0}
]

let set_drag (w : GObj.drag_ops) =
  w#dest_set drop_targets ~actions:[`COPY;`MOVE];
  w#connect#data_received ~callback:drop_received

(** Session management *)

let create_session f =
  let project_file, args = make_coqtop_args f in
  if project_file <> "" then
    flash_info (Printf.sprintf "Reading options from %s" project_file);
  let ans = Session.create f args in
  let _ = set_drag ans.script#drag in
  ans

(** Auxiliary functions for the File operations *)

module FileAux = struct

let load_file ?(maycreate=false) f =
  let f = CUnix.correct_path f (Sys.getcwd ()) in
  try
    Minilib.log "Loading file starts";
    let is_f = CUnix.same_file f in
    let rec search_f i = function
      | [] -> false
      | sn :: sessions ->
        match sn.fileops#filename with
	  | Some fn when is_f fn -> notebook#goto_page i; true
          | _ -> search_f (i+1) sessions
    in
    if not (search_f 0 notebook#pages) then begin
      Minilib.log "Loading: get raw content";
      let b = Buffer.create 1024 in
      if Sys.file_exists f then Ideutils.read_file f b
      else if not maycreate then flash_info ("Load failed: no such file");
      Minilib.log "Loading: convert content";
      let s = do_convert (Buffer.contents b) in
      Minilib.log "Loading: create view";
      let session = create_session (Some f) in
      let index = notebook#append_term session in
      notebook#goto_page index;
      Minilib.log "Loading: stats";
      session.fileops#update_stats;
      let input_buffer = session.buffer in
      Minilib.log "Loading: fill buffer";
      input_buffer#set_text s;
      input_buffer#set_modified false;
      input_buffer#place_cursor ~where:input_buffer#start_iter;
      Sentence.tag_all input_buffer;
      session.script#clear_undo ();
      Minilib.log "Loading: success";
    end
  with e -> flash_info ("Load failed: "^(Printexc.to_string e))

let confirm_save ok =
  if ok then flash_info "Saved" else warning "Save Failed"

let select_and_save ~saveas ?filename sn =
  let do_save = if saveas then sn.fileops#saveas else sn.fileops#save in
  let title = if saveas then "Save file as" else "Save file" in
  match select_file_for_save ~title ?filename () with
    |None -> false
    |Some f ->
      let ok = do_save f in
      confirm_save ok;
      if ok then sn.tab_label#set_text (Filename.basename f);
      ok

let check_save ~saveas sn =
  try match sn.fileops#filename with
    |None -> select_and_save ~saveas sn
    |Some f ->
      let ok = sn.fileops#save f in
      confirm_save ok;
      ok
  with _ -> warning "Save Failed"; false

exception DontQuit

let check_quit saveall =
  (try save_pref () with _ -> flash_info "Cannot save preferences");
  let is_modified sn = sn.buffer#modified in
  if List.exists is_modified notebook#pages then begin
    let answ = GToolbox.question_box ~title:"Quit"
      ~buttons:["Save Named Buffers and Quit";
                "Quit without Saving";
                "Don't Quit"]
      ~default:0
      ~icon:(warn_image ())#coerce
      "There are unsaved buffers"
    in
    match answ with
      | 1 -> saveall ()
      | 2 -> ()
      | _ -> raise DontQuit
  end;
  List.iter (fun sn -> Coq.close_coqtop sn.coqtop) notebook#pages

(* For MacOS, just to be sure, we close all coqtops (again?) *)
let close_and_quit () =
  List.iter (fun sn -> Coq.close_coqtop sn.coqtop) notebook#pages;
  exit 0

let crash_save exitcode =
  Minilib.log "Starting emergency save of buffers in .crashcoqide files";
  let idx =
    let r = ref 0 in
    fun () -> incr r; string_of_int !r
  in
  let save_session sn =
    let filename = match sn.fileops#filename with
      | None -> "Unnamed_coqscript_" ^ idx () ^ ".crashcoqide"
      | Some f -> f^".crashcoqide"
    in
    try
      if try_export filename (sn.buffer#get_text ()) then
	Minilib.log ("Saved "^filename)
      else Minilib.log ("Could not save "^filename)
    with _ -> Minilib.log ("Could not save "^filename)
  in
  List.iter save_session notebook#pages;
  Minilib.log "End emergency save";
  exit exitcode

end

let () = load_file_cb := (fun s -> FileAux.load_file s)

(** Callbacks for the File menu *)

module File = struct

let newfile _ =
  let session = create_session None in
  let index = notebook#append_term session in
  notebook#goto_page index

let load _ =
  let filename =
    try notebook#current_term.fileops#filename
    with Invalid_argument _ -> None in
  match select_file_for_open ~title:"Load file" ?filename () with
    | None -> ()
    | Some f -> FileAux.load_file f

let save _ = on_current_term (FileAux.check_save ~saveas:false)

let saveas sn =
  try
    let filename = sn.fileops#filename in
    ignore (FileAux.select_and_save ~saveas:true ?filename sn)
  with _ -> warning "Save Failed"

let saveas = cb_on_current_term saveas

let saveall _ =
  List.iter
    (fun sn -> match sn.fileops#filename with
      | None -> ()
      | Some f -> ignore (sn.fileops#save f))
    notebook#pages

let () = Coq.save_all := saveall

let revert_all _ =
  List.iter
    (fun sn -> if sn.fileops#changed_on_disk then sn.fileops#revert)
    notebook#pages

let quit _ =
  try FileAux.check_quit saveall; exit 0
  with FileAux.DontQuit -> ()

let close_buffer sn =
  let do_remove () = notebook#remove_page notebook#current_page in
  if not sn.buffer#modified then do_remove ()
  else
    let answ = GToolbox.question_box ~title:"Close"
      ~buttons:["Save Buffer and Close";
                "Close without Saving";
                "Don't Close"]
      ~default:0
      ~icon:(warn_image ())#coerce
      "This buffer has unsaved modifications"
    in
    match answ with
      | 1 when FileAux.check_save ~saveas:true sn -> do_remove ()
      | 2 -> do_remove ()
      | _ -> ()

let close_buffer = cb_on_current_term close_buffer

let export kind sn =
  match sn.fileops#filename with
    |None -> flash_info "Cannot print: this buffer has no name"
    |Some f ->
      let basef = Filename.basename f in
      let output =
        let basef_we = try Filename.chop_extension basef with _ -> basef in
        match kind with
          | "latex" -> basef_we ^ ".tex"
          | "dvi" | "ps" | "pdf" | "html" -> basef_we ^ "." ^ kind
          | _ -> assert false
      in
      let cmd =
        local_cd f ^ cmd_coqdoc#get ^ " --" ^ kind ^ " -o " ^
        (Filename.quote output) ^ " " ^ (Filename.quote basef) ^ " 2>&1"
      in
      sn.messages#default_route#set (Pp.str ("Running: "^cmd));
      let finally st = flash_info (cmd ^ pr_exit_status st)
      in
      run_command (fun msg -> sn.messages#default_route#add_string msg) finally cmd

let export kind = cb_on_current_term (export kind)

let print sn =
  match sn.fileops#filename with
    |None -> flash_info "Cannot print: this buffer has no name"
    |Some f_name ->
      let cmd =
        local_cd f_name ^ cmd_coqdoc#get ^ " -ps " ^
        Filename.quote (Filename.basename f_name) ^ " | " ^ cmd_print#get
      in
      let w = GWindow.window ~title:"Print" ~modal:true
        ~position:`CENTER ~wm_class:"CoqIDE" ~wm_name: "CoqIDE" ()
      in
      let v = GPack.vbox ~spacing:10 ~border_width:10 ~packing:w#add ()
      in
      let _ = GMisc.label ~text:"Print using the following command:"
        ~justify:`LEFT ~packing:v#add ()
      in
      let e = GEdit.entry ~text:cmd ~editable:true ~width_chars:80
        ~packing:v#add ()
      in
      let h = GPack.hbox ~spacing:10 ~packing:v#add ()
      in
      let ko = GButton.button ~stock:`CANCEL ~label:"Cancel" ~packing:h#add ()
      in
      let ok = GButton.button ~stock:`PRINT ~label:"Print" ~packing:h#add ()
      in
      let callback_print () =
        w#destroy ();
        let cmd = e#text in
        let finally st = flash_info (cmd ^ pr_exit_status st) in
        run_command ignore finally cmd
      in
      let _ = ko#connect#clicked ~callback:w#destroy in
      let _ = ok#connect#clicked ~callback:callback_print in
      w#misc#show ()

let print = cb_on_current_term print

let highlight sn =
  Sentence.tag_all sn.buffer;
  sn.script#recenter_insert

let highlight = cb_on_current_term highlight

end

(** Timers *)

let reset_revert_timer () =
  FileOps.revert_timer.kill ();
  if global_auto_revert#get then
    FileOps.revert_timer.run
      ~ms:global_auto_revert_delay#get
      ~callback:(fun () -> File.revert_all (); true)

let reset_autosave_timer () =
  let autosave sn = try sn.fileops#auto_save with _ -> () in
  let autosave_all () = List.iter autosave notebook#pages; true in
  FileOps.autosave_timer.kill ();
  if auto_save#get then
    FileOps.autosave_timer.run ~ms:auto_save_delay#get ~callback:autosave_all

(** Export of functions used in [coqide_main] : *)

let forbid_quit () =
  try FileAux.check_quit File.saveall; false
  with FileAux.DontQuit -> true

let close_and_quit = FileAux.close_and_quit
let crash_save = FileAux.crash_save
let do_load f = FileAux.load_file f

(** Callbacks for external commands *)

module External = struct

let coq_makefile sn =
  match sn.fileops#filename with
    |None -> flash_info "Cannot make makefile: this buffer has no name"
    |Some f ->
      let cmd = local_cd f ^ cmd_coqmakefile#get in
      let finally st = flash_info (cmd_coqmakefile#get ^ pr_exit_status st)
      in
      run_command ignore finally cmd

let coq_makefile = cb_on_current_term coq_makefile

let editor sn =
  match sn.fileops#filename with
    |None -> warning "Call to external editor available only on named files"
    |Some f ->
      File.save ();
      let f = Filename.quote f in
      let cmd = Util.subst_command_placeholder cmd_editor#get f in
      run_command ignore (fun _ -> sn.fileops#revert) cmd

let editor = cb_on_current_term editor

let compile sn =
  File.save ();
  match sn.fileops#filename with
    |None -> flash_info "Active buffer has no name"
    |Some f ->
      let args = Coq.get_arguments sn.coqtop in
      let cmd = cmd_coqc#get 
	^ " " ^ String.concat " " args
	^ " " ^ (Filename.quote f) ^ " 2>&1"
      in
      let buf = Buffer.create 1024 in
      sn.messages#default_route#set (Pp.str ("Running: "^cmd));
      let display s =
        sn.messages#default_route#add_string s;
        Buffer.add_string buf s
      in
      let finally st =
        if st = Unix.WEXITED 0 then
          flash_info (f ^ " successfully compiled")
        else begin
          flash_info (f ^ " failed to compile");
          sn.messages#default_route#set (Pp.str "Compilation output:\n");
          sn.messages#default_route#add (Pp.str (Buffer.contents buf));
        end
      in
      run_command display finally cmd

let compile = cb_on_current_term compile

(** [last_make_buf] contains the output of the last make compilation.
    [last_make] is the same, but as a string, refreshed only when searching
    the next error. *)

let last_make_buf = Buffer.create 1024
let last_make = ref ""
let last_make_index = ref 0
let last_make_dir = ref ""

let make sn =
  match sn.fileops#filename with
    |None -> flash_info "Cannot make: this buffer has no name"
    |Some f ->
      File.saveall ();
      let cmd = local_cd f ^ cmd_make#get ^ " 2>&1" in
      sn.messages#default_route#set (Pp.str "Compilation output:\n");
      Buffer.reset last_make_buf;
      last_make := "";
      last_make_index := 0;
      last_make_dir := Filename.dirname f;
      let display s =
        sn.messages#default_route#add_string s;
        Buffer.add_string last_make_buf s
      in
      let finally st = flash_info (cmd_make#get ^ pr_exit_status st)
      in
      run_command display finally cmd

let make = cb_on_current_term make

let search_compile_error_regexp =
  Str.regexp
    "File \"\\([^\"]+\\)\", line \\([0-9]+\\), characters \\([0-9]+\\)-\\([0-9]+\\)"

let search_next_error () =
  if String.length !last_make <> Buffer.length last_make_buf
  then last_make := Buffer.contents last_make_buf;
  let _ =
    Str.search_forward search_compile_error_regexp !last_make !last_make_index
  in
  let f = Str.matched_group 1 !last_make
  and l = int_of_string (Str.matched_group 2 !last_make)
  and b = int_of_string (Str.matched_group 3 !last_make)
  and e = int_of_string (Str.matched_group 4 !last_make)
  and msg_index = Str.match_beginning ()
  in
  last_make_index := Str.group_end 4;
  (Filename.concat !last_make_dir f, l, b, e,
   String.sub !last_make msg_index (String.length !last_make - msg_index))

let next_error sn =
  try
    let file,line,start,stop,error_msg = search_next_error () in
    FileAux.load_file file;
    let b = sn.buffer in
    let starti = b#get_iter_at_byte ~line:(line-1) start in
    let stopi = b#get_iter_at_byte ~line:(line-1) stop in
    b#apply_tag Tags.Script.error ~start:starti ~stop:stopi;
    b#place_cursor ~where:starti;
    sn.messages#default_route#set (Pp.str error_msg);
    sn.script#misc#grab_focus ()
  with Not_found ->
    last_make_index := 0;
    sn.messages#default_route#set (Pp.str "No more errors.\n")

let next_error = cb_on_current_term next_error

end

(** Callbacks for the Navigation menu *)

let update_status sn =
  let display msg = pop_info (); push_info msg in
  let next = function
  | Interface.Fail x -> sn.coqops#handle_failure x
  | Interface.Good status ->
    let path = match status.Interface.status_path with
      | [] | _ :: [] -> "" (* Drop the topmost level, usually "Top" *)
      | _ :: l -> " in " ^ String.concat "." l
    in
    let name = match status.Interface.status_proofname with
      | None -> ""
      | Some n -> ", proving " ^ n
    in
    display ("Ready"^ (if nanoPG#get then ", [μPG]" else "") ^ path ^ name);
    Coq.return ()
  in
  Coq.bind (Coq.status false) next

let find_next_occurrence ~backward sn =
  (** go to the next occurrence of the current word, forward or backward *)
  let b = sn.buffer in
  let start = find_word_start (b#get_iter_at_mark `INSERT) in
  let stop = find_word_end start in
  let text = b#get_text ~start ~stop () in
  let search = if backward then start#backward_search else stop#forward_search
  in
  match search text with
    |None -> ()
    |Some(where, _) -> b#place_cursor ~where; sn.script#recenter_insert

let send_to_coq_aux f sn =
  let info () = Minilib.log ("Coq busy, discarding query") in
  let f = Coq.seq (f sn) (update_status sn) in
  Coq.try_grab sn.coqtop f info

let send_to_coq f = on_current_term (send_to_coq_aux f)

module Nav = struct
  let forward_one _ = send_to_coq (fun sn -> sn.coqops#process_next_phrase)
  let backward_one _ = send_to_coq (fun sn -> sn.coqops#backtrack_last_phrase)
  let goto _ = send_to_coq (fun sn -> sn.coqops#go_to_insert)
  let goto_end _ = send_to_coq (fun sn -> sn.coqops#process_until_end_or_error)
  let previous_occ = cb_on_current_term (find_next_occurrence ~backward:true)
  let next_occ = cb_on_current_term (find_next_occurrence ~backward:false)
  let restart sn =
    Minilib.log "Reset Initial";
    Coq.reset_coqtop sn.coqtop
  let restart _ = on_current_term restart
  let interrupt sn =
    Minilib.log "User break received";
    Coq.break_coqtop sn.coqtop CString.(Set.elements (Map.domain sn.jobpage#data))
  let interrupt = cb_on_current_term interrupt
  let join_document _ = send_to_coq (fun sn -> sn.coqops#join_document)
end

let tactic_wizard_callback l _ =
  send_to_coq (fun sn -> sn.coqops#tactic_wizard l)

let printopts_callback opts v =
  let b = v#get_active in
  let () = List.iter (fun o -> Coq.PrintOpt.set o b) opts in
  send_to_coq (fun sn -> sn.coqops#show_goals)

(** Templates menu *)

let get_current_word term =
  (** First look to find if autocompleting *)
  match term.script#complete_popup#proposal with
  | Some p -> p
  | None ->
  (** Then look at the current selected word *)
  let buf1 = term.script#buffer in
  let buf2 = term.proof#buffer in
  if buf1#has_selection then
    let (start, stop) = buf1#selection_bounds in
    buf1#get_text ~slice:true ~start ~stop ()
  else if buf2#has_selection then
    let (start, stop) = buf2#selection_bounds in
    buf2#get_text ~slice:true ~start ~stop ()
  else if term.messages#has_selection then
    term.messages#get_selected_text
  (** Otherwise try to find the word around the cursor *)
  else
    let it = term.script#buffer#get_iter_at_mark `INSERT in
    let start = find_word_start it in
    let stop = find_word_end start in
    term.script#buffer#get_text ~slice:true ~start ~stop ()

let print_branch c l =
  Format.fprintf c " | @[<hov 1>%a@]=> _@\n"
    (Minilib.print_list (fun c s -> Format.fprintf c "%s@ " s)) l

let print_branches c cases =
  Format.fprintf c "@[match var with@\n%aend@]@."
    (Minilib.print_list print_branch) cases

let display_match sn = function
  |Interface.Fail _ ->
    flash_info "Not an inductive type"; Coq.return ()
  |Interface.Good cases ->
    let text =
      let buf = Buffer.create 1024 in
      let () = print_branches (Format.formatter_of_buffer buf) cases in
      Buffer.contents buf
    in
    Minilib.log ("match template :\n" ^ text);
    let b = sn.buffer in
    let _ =  b#delete_selection () in
    let m = b#create_mark (b#get_iter_at_mark `INSERT) in
    if b#insert_interactive text then begin
      let i = b#get_iter (`MARK m) in
      let _ = i#nocopy#forward_chars 9 in
      let _ = b#place_cursor ~where:i in
      b#move_mark ~where:(i#backward_chars 3) `SEL_BOUND
    end;
    b#delete_mark (`MARK m);
    Coq.return ()

let match_callback sn =
  let w = get_current_word sn in
  let coqtop = sn.coqtop in
  let query = Coq.bind (Coq.mkcases w) (display_match sn) in
  Coq.try_grab coqtop query ignore

let match_callback = cb_on_current_term match_callback

(** Queries *)

module Query = struct

let doquery query sn =
  sn.messages#default_route#clear;
  Coq.try_grab sn.coqtop (sn.coqops#raw_coq_query query ~route_id:0
    ~next:(function
        | Interface.Fail (_, _, err) ->
            let err = Ideutils.validate err in
            sn.messages#default_route#add err;
            Coq.return ()
        | Interface.Good () -> Coq.return ()))
  ignore

let queryif command sn =
  Option.iter (fun query -> doquery (query ^ ".") sn)
    begin try
      let i = CString.string_index_from command 0 "..." in
      let word = get_current_word sn in
      if word = "" then None
      else Some (CString.sub command 0 i ^ " " ^ word)
    with Not_found -> Some command end

let query command _ = cb_on_current_term (queryif command) ()

end

(** Misc *)

module MiscMenu = struct

let detach_view sn = sn.control#detach ()

let detach_view = cb_on_current_term detach_view

let log_file_message () =
  if !Minilib.debug then
    let file = match !logfile with None -> "stderr" | Some f -> f in
    "\nDebug mode is on, log file is "^file
  else ""

let initial_about () =
  let initial_string =
    "Welcome to CoqIDE, an Integrated Development Environment for Coq"
  in
  let coq_version = Coq.short_version () in
  let version_info =
    if Glib.Utf8.validate coq_version then
      "\nYou are running " ^ coq_version
    else ""
  in
  let msg = initial_string ^ version_info ^ log_file_message () in
  on_current_term (fun term -> term.messages#default_route#add_string msg)

let coq_icon () =
  (* May raise Nof_found *)
  let name = "coq.png" in
  let chk d = Sys.file_exists (Filename.concat d name) in
  let dir = List.find chk (Minilib.coqide_data_dirs ()) in
  Filename.concat dir name

let about _ =
  let dialog = GWindow.about_dialog () in
  let _ = dialog#connect#response ~callback:(fun _ -> dialog#destroy ()) in
  let _ =
    try dialog#set_logo (GdkPixbuf.from_file (coq_icon ()))
    with _ -> ()
  in
  let copyright =
    "Coq is developed by the Coq Development Team\n\
     (INRIA - CNRS - LIX - LRI - PPS)"
  in
  let authors = [
    "Benjamin Monate";
    "Jean-Christophe Filliâtre";
    "Pierre Letouzey";
    "Claude Marché";
    "Bruno Barras";
    "Pierre Corbineau";
    "Julien Narboux";
    "Hugo Herbelin";
    "Enrico Tassi";
    ]
  in
  dialog#set_name "CoqIDE";
  dialog#set_comments "The Coq Integrated Development Environment";
  dialog#set_website Coq_config.wwwcoq;
  dialog#set_version Coq_config.version;
  dialog#set_copyright copyright;
  dialog#set_authors authors;
  dialog#show ()

let comment = cb_on_current_term (fun t -> t.script#comment ())
let uncomment = cb_on_current_term (fun t -> t.script#uncomment ())

let coqtop_arguments sn =
  let dialog = GWindow.dialog ~title:"Coqtop arguments" () in
  let coqtop = sn.coqtop in
  (** Text entry *)
  let args = Coq.get_arguments coqtop in
  let text = String.concat " " args in
  let entry = GEdit.entry ~text ~packing:dialog#vbox#add () in
  (** Buttons *)
  let box = dialog#action_area in
  let ok = GButton.button ~stock:`OK ~packing:box#add () in
  let ok_cb () =
    let nargs = CString.split ' ' entry#text in
    if nargs <> args then
      let failed = Coq.filter_coq_opts nargs in
      match failed with
      | [] ->
        let () = Coq.set_arguments coqtop nargs in
        dialog#destroy ()
      | args ->
        let args = String.concat " " args in
        let msg = Printf.sprintf "Invalid arguments: %s" args in
        let () = sn.messages#default_route#clear in
        sn.messages#default_route#push Feedback.Error (Pp.str msg)
    else dialog#destroy ()
  in
  let _ = entry#connect#activate ~callback:ok_cb in
  let _ = ok#connect#clicked ~callback:ok_cb in
  let cancel = GButton.button ~stock:`CANCEL ~packing:box#add () in
  let cancel_cb () = dialog#destroy () in
  let _ = cancel#connect#clicked ~callback:cancel_cb in
  dialog#show ()

let coqtop_arguments = cb_on_current_term coqtop_arguments

let show_hide_query_pane sn =
  let ccw = sn.command in
  if ccw#visible then ccw#hide else ccw#show

let zoom_fit sn =
  let script = sn.script in
  let space = script#misc#allocation.Gtk.width in
  let cols = script#right_margin_position in
  let pango_ctx = script#misc#pango_context in
  let layout = pango_ctx#create_layout in
  let fsize = Pango.Font.get_size (Pango.Font.from_string text_font#get) in
  Pango.Layout.set_text layout (String.make cols 'X');
  let tlen = fst (Pango.Layout.get_pixel_size layout) in
  Pango.Font.set_size (Pango.Font.from_string text_font#get)
    (fsize * space / tlen / Pango.scale * Pango.scale);
  save_pref ()

end

(** Refresh functions *)

let refresh_notebook_pos () =
  let pos = match vertical_tabs#get, opposite_tabs#get with
    | false, false -> `TOP
    | false, true  -> `BOTTOM
    | true , false -> `LEFT
    | true , true  -> `RIGHT
  in
  notebook#set_tab_pos pos

(** Wrappers around GAction functions for creating menus *)

let menu = GAction.add_actions
let item = GAction.add_action
let radio = GAction.add_radio_action

(** Toggle items in menus for printing options *)

let toggle_item = GAction.add_toggle_action

(** Search the first '_' in a label string and return the following
    character as shortcut, plus the string without the '_' *)

let get_shortcut s =
  try
    let n = String.length s in
    let i = String.index s '_' in
    let k = String.make 1 s.[i+1] in
    let s' = (String.sub s 0 i) ^ (String.sub s (i+1) (n-i-1)) in
    Some k, s'
  with _ -> None,s

module Opt = Coq.PrintOpt

let toggle_items menu_name l =
  let f d =
    let label = d.Opt.label in
    let k, name = get_shortcut label in
    let accel = Option.map ((^) modifier_for_display#get) k in
    toggle_item name ~label ?accel ~active:d.Opt.init
      ~callback:(printopts_callback d.Opt.opts)
      menu_name
  in
  List.iter f l

let no_under = Util.String.map (fun x -> if x = '_' then '-' else x)

(** Create alphabetical menu items with elements in sub-items.
    [l] is a list of lists, one per initial letter *)

let alpha_items menu_name item_name l =
  let mk_item text =
    let text' =
      let last = String.length text - 1 in
      if text.[last] = '.'
      then text ^"\n"
      else text ^" "
    in
    let callback _ =
      on_current_term (fun sn -> sn.buffer#insert_interactive text')
    in
    item (item_name^" "^(no_under text)) ~label:text ~callback menu_name
  in
  let mk_items = function
    | [] -> ()
    | [s] -> mk_item s
    | s::_ as ll ->
      let name = Printf.sprintf "%s %c" item_name s.[0] in
      let label = Printf.sprintf "_%c..." s.[0] in
      item name ~label menu_name;
      List.iter mk_item ll
  in
  List.iter mk_items l

(** Create a menu item that will insert a given text,
    and select the zone given by (offset,len).
    The first word in the text is used as item keyword.
    Caveat: the offset is now from the start of the text. *)

let template_item (text, offset, len, key) =
  let modifier = modifier_for_templates#get in
  let idx = String.index text ' ' in
  let name = String.sub text 0 idx in
  let label = "_"^name^" __" in
  let negoffset = String.length text - offset - len in
  let callback sn =
    let b = sn.buffer in
    if b#insert_interactive text then begin
      let iter = b#get_iter_at_mark `INSERT in
      ignore (iter#nocopy#backward_chars negoffset);
      b#move_mark `INSERT ~where:iter;
      ignore (iter#nocopy#backward_chars len);
      b#move_mark `SEL_BOUND ~where:iter;
    end
  in
  item name ~label ~callback:(cb_on_current_term callback) ~accel:(modifier^key)

(** Create menu items for pairs (query, shortcut key). *)
let user_queries_items menu_name item_name l =
  let mk_item (query, key) =
    let callback = Query.query query in
    let accel = if not (CString.is_empty key) then
      Some (modifier_for_queries#get^key) else None in
    item (item_name^" "^(no_under query)) ~label:query ?accel ~callback menu_name
  in
  List.iter mk_item l

let emit_to_focus window sgn =
  let focussed_widget = GtkWindow.Window.get_focus window#as_window in
  let obj = Gobject.unsafe_cast focussed_widget in
  try GtkSignal.emit_unit obj ~sgn with _ -> ()

(** {2 Creation of the main coqide window } *)

let build_ui () =
  let w = GWindow.window
    ~wm_class:"CoqIde" ~wm_name:"CoqIde"
    ~width:window_width#get ~height:window_height#get
    ~title:"CoqIde" ()
  in
  let () =
    try w#set_icon (Some (GdkPixbuf.from_file (MiscMenu.coq_icon ())))
    with _ -> ()
  in
  let _ = w#event#connect#delete ~callback:(fun _ -> File.quit (); true) in
  let _ = set_drag w#drag in

  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  let file_menu = GAction.action_group ~name:"File" () in
  let edit_menu = GAction.action_group ~name:"Edit" () in
  let view_menu = GAction.action_group ~name:"View" () in
  let export_menu = GAction.action_group ~name:"Export" () in
  let navigation_menu = GAction.action_group ~name:"Navigation" () in
  let tactics_menu = GAction.action_group ~name:"Tactics" () in
  let templates_menu = GAction.action_group ~name:"Templates" () in
  let tools_menu = GAction.action_group ~name:"Tools" () in
  let queries_menu = GAction.action_group ~name:"Queries" () in
  let compile_menu = GAction.action_group ~name:"Compile" () in
  let windows_menu = GAction.action_group ~name:"Windows" () in
  let help_menu = GAction.action_group ~name:"Help" () in
  let all_menus = [
    file_menu; edit_menu; view_menu; export_menu; navigation_menu; tactics_menu;
    templates_menu; tools_menu; queries_menu; compile_menu; windows_menu;
    help_menu; ] in

  menu file_menu [
    item "File" ~label:"_File";
    item "New" ~callback:File.newfile ~stock:`NEW;
    item "Open" ~callback:File.load ~stock:`OPEN;
    item "Save" ~callback:File.save ~stock:`SAVE ~tooltip:"Save current buffer";
    item "Save as" ~label:"S_ave as" ~stock:`SAVE_AS ~callback:File.saveas;
    item "Save all" ~label:"Sa_ve all" ~callback:File.saveall;
    item "Revert all buffers" ~label:"_Revert all buffers"
      ~callback:File.revert_all ~stock:`REVERT_TO_SAVED;
    item "Close buffer" ~label:"_Close buffer" ~stock:`CLOSE
      ~callback:File.close_buffer ~tooltip:"Close current buffer";
    item "Print..." ~label:"_Print..."
      ~callback:File.print ~stock:`PRINT ~accel:"<Ctrl>p";
    item "Rehighlight" ~label:"Reh_ighlight" ~accel:"<Ctrl>l"
      ~callback:File.highlight ~stock:`REFRESH;
    item "Quit" ~stock:`QUIT ~callback:File.quit;
  ];

  menu export_menu [
    item "Export to" ~label:"E_xport to";
    item "Html" ~label:"_Html" ~callback:(File.export "html");
    item "Latex" ~label:"_LaTeX" ~callback:(File.export "latex");
    item "Dvi" ~label:"_Dvi" ~callback:(File.export "dvi");
    item "Pdf" ~label:"_Pdf" ~callback:(File.export "pdf");
    item "Ps" ~label:"_Ps" ~callback:(File.export "ps");
  ];

  menu edit_menu [
    item "Edit" ~label:"_Edit";
    item "Undo" ~accel:"<Ctrl>u" ~stock:`UNDO
      ~callback:(cb_on_current_term (fun t -> t.script#undo ()));
    item "Redo" ~stock:`REDO
      ~callback:(cb_on_current_term (fun t -> t.script#redo ()));
    item "Cut" ~stock:`CUT
      ~callback:(fun _ -> emit_to_focus w GtkText.View.S.cut_clipboard);
    item "Copy" ~stock:`COPY
      ~callback:(fun _ -> emit_to_focus w GtkText.View.S.copy_clipboard);
    item "Paste" ~stock:`PASTE
      ~callback:(fun _ -> emit_to_focus w GtkText.View.S.paste_clipboard);
    item "Find" ~stock:`FIND ~label:"Find / Replace"
      ~callback:(cb_on_current_term (fun t -> t.finder#show ()));
    item "Find Next" ~label:"Find _Next" ~stock:`GO_DOWN ~accel:"F3"
      ~callback:(cb_on_current_term (fun t -> t.finder#find_forward ()));
    item "Find Previous" ~label:"Find _Previous" ~stock:`GO_UP
      ~accel:"<Shift>F3"
      ~callback:(cb_on_current_term (fun t -> t.finder#find_backward ()));
    item "External editor" ~label:"External editor" ~stock:`EDIT
      ~callback:External.editor;
    item "Preferences" ~accel:"<Ctrl>comma" ~stock:`PREFERENCES
      ~callback:(fun _ ->
        begin
	  try Preferences.configure ~apply:refresh_notebook_pos ()
	  with _ -> flash_info "Cannot save preferences"
        end;
        reset_revert_timer ());
  ];

  menu view_menu [
    item "View" ~label:"_View";
    item "Previous tab" ~label:"_Previous tab" ~accel:"<Alt>Left"
      ~stock:`GO_BACK
      ~callback:(fun _ -> notebook#previous_page ());
    item "Next tab" ~label:"_Next tab" ~accel:"<Alt>Right"
      ~stock:`GO_FORWARD
      ~callback:(fun _ -> notebook#next_page ());
    item "Zoom in" ~label:"_Zoom in" ~accel:("<Control>plus")
        ~stock:`ZOOM_IN ~callback:(fun _ ->
          let ft = Pango.Font.from_string text_font#get in
          Pango.Font.set_size ft (Pango.Font.get_size ft + Pango.scale);
          text_font#set (Pango.Font.to_string ft);
          save_pref ());
    item "Zoom out" ~label:"_Zoom out" ~accel:("<Control>minus")
        ~stock:`ZOOM_OUT ~callback:(fun _ ->
          let ft = Pango.Font.from_string text_font#get in
          Pango.Font.set_size ft (Pango.Font.get_size ft - Pango.scale);
          text_font#set (Pango.Font.to_string ft);
          save_pref ());
    item "Zoom fit" ~label:"_Zoom fit" ~accel:("<Control>0")
        ~stock:`ZOOM_FIT ~callback:(cb_on_current_term MiscMenu.zoom_fit);
    toggle_item "Show Toolbar" ~label:"Show _Toolbar"
      ~active:(show_toolbar#get)
      ~callback:(fun _ -> show_toolbar#set (not show_toolbar#get));
    item "Query Pane" ~label:"_Query Pane"
      ~accel:"F1"
      ~callback:(cb_on_current_term MiscMenu.show_hide_query_pane);
    GAction.group_radio_actions
      ~init_value:(
        let v = diffs#get in
        List.iter (fun o -> Opt.set o v) Opt.diff_item.Opt.opts;
        if v = "on" then 1
        else if v = "removed" then 2
        else 0)
      ~callback:begin fun n ->
        (match n with
        | 0 -> List.iter (fun o -> Opt.set o "off"; diffs#set "off") Opt.diff_item.Opt.opts
        | 1 -> List.iter (fun o -> Opt.set o "on"; diffs#set "on") Opt.diff_item.Opt.opts
        | 2 -> List.iter (fun o -> Opt.set o "removed"; diffs#set "removed") Opt.diff_item.Opt.opts
        | _ -> assert false);
        send_to_coq (fun sn -> sn.coqops#show_goals)
        end
      [
        radio "Unset diff" 0 ~label:"_Don't show diffs";
        radio "Set diff" 1 ~label:"Show diffs: only _added";
        radio "Set removed diff" 2 ~label:"Show diffs: added and _removed";
      ];
  ];
  toggle_items view_menu Coq.PrintOpt.bool_items;

  let navitem (text, label, stock, callback, tooltip, accel) =
    let accel = modifier_for_navigation#get ^ accel in
    item text ~label ~stock ~callback ~tooltip ~accel
  in
  menu navigation_menu begin
  [
    (fun e -> item "Navigation" ~label:"_Navigation" e);
  ] @ List.map navitem [
    ("Forward", "_Forward", `GO_DOWN, Nav.forward_one, "Forward one command", "Down");
    ("Backward", "_Backward", `GO_UP, Nav.backward_one, "Backward one command", "Up");
    ("Go to", "_Go to", `JUMP_TO, Nav.goto, "Go to cursor", "Right");
    ("Start", "_Start", `GOTO_TOP, Nav.restart, "Restart coq", "Home");
    ("End", "_End", `GOTO_BOTTOM, Nav.goto_end, "Go to end", "End");
    ("Interrupt", "_Interrupt", `STOP, Nav.interrupt, "Interrupt computations", "Break");
    (* wait for this available in GtkSourceView !
    ("Hide", "_Hide", `MISSING_IMAGE,
        ~callback:(fun _ -> let sess = notebook#current_term in
          toggle_proof_visibility sess.buffer sess.analyzed_view#get_insert), "Hide proof", "h"); *)
    ("Previous", "_Previous", `GO_BACK, Nav.previous_occ, "Previous occurrence", "less");
    ("Next", "_Next", `GO_FORWARD, Nav.next_occ, "Next occurrence", "greater");
    ("Force", "_Force", `EXECUTE, Nav.join_document, "Fully check the document", "f");
  ] end;

  let tacitem s sc =
    item s ~label:("_"^s)
      ~accel:(modifier_for_tactics#get^sc)
      ~callback:(tactic_wizard_callback [s])
  in
  menu tactics_menu [
    item "Try Tactics" ~label:"_Try Tactics";
    item "Wizard" ~label:"<Proof Wizard>" ~stock:`DIALOG_INFO
      ~tooltip:"Proof Wizard" ~accel:(modifier_for_tactics#get^"dollar")
      ~callback:(tactic_wizard_callback automatic_tactics#get);
    tacitem "auto" "a";
    tacitem "auto with *" "asterisk";
    tacitem "eauto" "e";
    tacitem "eauto with *" "ampersand";
    tacitem "intuition" "i";
    tacitem "omega" "o";
    tacitem "simpl" "s";
    tacitem "tauto" "p";
    tacitem "trivial" "v";
  ];
  alpha_items tactics_menu "Tactic" Coq_commands.tactics;

  menu templates_menu [
    item "Templates" ~label:"Te_mplates";
    template_item ("Lemma new_lemma : .\nProof.\n\nQed.\n", 6,9, "J");
    template_item ("Theorem new_theorem : .\nProof.\n\nQed.\n", 8,11, "T");
    template_item ("Definition ident := .\n", 11,5, "E");
    template_item ("Inductive ident : :=\n  | : .\n", 10,5, "I");
    template_item ("Fixpoint ident (_ : _) {struct _} : _ :=\n.\n", 9,5, "F");
    template_item ("Scheme new_scheme := Induction for _ Sort _\n" ^
                   "with _ := Induction for _ Sort _.\n", 7,10, "S");
    item "match" ~label:"match ..." ~accel:(modifier_for_templates#get^"M")
      ~callback:match_callback
  ];
  alpha_items templates_menu "Template" Coq_commands.commands;

  let qitem s sc =
    let query = s ^ "..." in
    item s ~label:("_"^s)
      ~accel:(modifier_for_queries#get^sc)
      ~callback:(Query.query query)
  in
  menu queries_menu [
    item "Queries" ~label:"_Queries";
    qitem "Search" "K";
    qitem "Check" "C";
    qitem "Print" "P";
    qitem "About" "A";
    qitem "Locate" "L";
    qitem "Print Assumptions" "N";
  ];
  user_queries_items queries_menu "User-Query" user_queries#get;

  menu tools_menu [
    item "Tools" ~label:"_Tools";
    item "Comment" ~label:"_Comment" ~accel:"<CTRL>D"
      ~callback:MiscMenu.comment;
    item "Uncomment" ~label:"_Uncomment" ~accel:"<CTRL><SHIFT>D"
      ~callback:MiscMenu.uncomment;
    item "Coqtop arguments" ~label:"Coqtop _arguments"
      ~callback:MiscMenu.coqtop_arguments;
  ];

  menu compile_menu [
    item "Compile" ~label:"_Compile";
    item "Compile buffer" ~label:"_Compile buffer" ~callback:External.compile;
    item "Make" ~label:"_Make" ~accel:"F6"
      ~callback:External.make;
    item "Next error" ~label:"_Next error" ~accel:"F7"
      ~callback:External.next_error;
    item "Make makefile" ~label:"Make makefile" ~callback:External.coq_makefile;
  ];

  menu windows_menu [
    item "Windows" ~label:"_Windows";
    item "Detach View" ~label:"Detach _View" ~callback:MiscMenu.detach_view
  ];

  menu help_menu [
    item "Help" ~label:"_Help";
    item "Browse Coq Manual" ~label:"Browse Coq _Manual"
      ~callback:(fun _ ->
        browse notebook#current_term.messages#default_route#add_string (doc_url ()));
    item "Browse Coq Library" ~label:"Browse Coq _Library"
      ~callback:(fun _ ->
        browse notebook#current_term.messages#default_route#add_string library_url#get);
    item "Help for keyword" ~label:"Help for _keyword" ~stock:`HELP
      ~callback:(fun _ -> on_current_term (fun sn ->
        browse_keyword sn.messages#default_route#add_string (get_current_word sn)));
    item "Help for μPG mode" ~label:"Help for μPG mode"
      ~callback:(fun _ -> on_current_term (fun sn ->
         sn.messages#default_route#clear;
         sn.messages#default_route#add_string (NanoPG.get_documentation ())));
    item "About Coq" ~label:"_About" ~stock:`ABOUT
      ~callback:MiscMenu.about
  ];

  Coqide_ui.init ();
  Coqide_ui.ui_m#insert_action_group file_menu 0;
  Coqide_ui.ui_m#insert_action_group export_menu 0;
  Coqide_ui.ui_m#insert_action_group edit_menu 0;
  Coqide_ui.ui_m#insert_action_group view_menu 0;
  Coqide_ui.ui_m#insert_action_group navigation_menu 0;
  Coqide_ui.ui_m#insert_action_group tactics_menu 0;
  Coqide_ui.ui_m#insert_action_group templates_menu 0;
  Coqide_ui.ui_m#insert_action_group tools_menu 0;
  Coqide_ui.ui_m#insert_action_group queries_menu 0;
  Coqide_ui.ui_m#insert_action_group compile_menu 0;
  Coqide_ui.ui_m#insert_action_group windows_menu 0;
  Coqide_ui.ui_m#insert_action_group help_menu 0;
  w#add_accel_group Coqide_ui.ui_m#get_accel_group ;
  GtkMain.Rc.parse_string "gtk-can-change-accels = 1";
  if Coq_config.gtk_platform <> `QUARTZ
  then vbox#pack (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar");

  (* Toolbar *)
  let tbar = GtkButton.Toolbar.cast
      ((Coqide_ui.ui_m#get_widget "/CoqIde ToolBar")#as_widget)
  in
  let () = GtkButton.Toolbar.set
    ~orientation:`HORIZONTAL ~style:`ICONS ~tooltips:true tbar
  in
  let toolbar = new GObj.widget tbar in
  let () = vbox#pack toolbar in

  (* Emacs/PG mode *)
  NanoPG.init w notebook all_menus;

  (* On tab switch, reset, update location *)
  let _ = notebook#connect#switch_page ~callback:(fun n ->
    let _ = if reset_on_tab_switch#get then Nav.restart () in
    try
      let session = notebook#get_nth_term n in
      let ins = session.buffer#get_iter_at_mark `INSERT in
      Ideutils.display_location ins
    with _ -> ())
  in

  (* Vertical Separator between Scripts and Goals *)
  let () = vbox#pack ~expand:true notebook#coerce in
  let () = refresh_notebook_pos () in
  let lower_hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
  let () = lower_hbox#pack ~expand:true status#coerce in
  let () = push_info ("Ready"^ if nanoPG#get then ", [μPG]" else "")  in

  (* Location display *)
  let l = GMisc.label
    ~text:"Line:     1 Char:   1"
    ~packing:lower_hbox#pack ()
  in
  let () = l#coerce#misc#set_name "location" in
  let () = set_location := l#set_text in

  (* Progress Bar *)
  let pbar = GRange.progress_bar ~pulse_step:0.1 () in
  let () = lower_hbox#pack pbar#coerce in
  let ready () = pbar#set_fraction 0.0; pbar#set_text "Coq is ready" in
  let pulse sn =
    if Coq.is_computing sn.coqtop then
      (pbar#set_text "Coq is computing"; pbar#pulse ())
    else ready () in
  let callback () = on_current_term pulse; true in
  let _ = Glib.Timeout.add ~ms:300 ~callback in

  (* Pending proofs.  It should be with a GtkSpinner... not bound *)
  let slaveinfo = GMisc.label ~xalign:0.5 ~width:50 () in
  let () = lower_hbox#pack slaveinfo#coerce in
  let () = slaveinfo#misc#set_has_tooltip true in
  let () = slaveinfo#misc#set_tooltip_markup
    "Proofs to be checked / Errors" in
  let update sn =
    let processed, to_process, jobs = sn.coqops#get_slaves_status in
    let missing = to_process - processed in
    let n_err = sn.coqops#get_n_errors in
    if n_err > 0 then
      slaveinfo#set_text (Printf.sprintf
        "%d / <span foreground=\"#FF0000\">%d</span>" missing n_err)
    else
      slaveinfo#set_text (Printf.sprintf "%d / %d" missing n_err);
    slaveinfo#set_use_markup true;
    sn.errpage#update sn.coqops#get_errors;
    sn.jobpage#update (Util.pi3 sn.coqops#get_slaves_status) in
  let callback () = on_current_term update; true in
  let _ = Glib.Timeout.add ~ms:300 ~callback in

  (* Initializing hooks *)
  let refresh_style style =
    let style = style_manager#style_scheme style in
    let iter_session v = v.script#source_buffer#set_style_scheme style in
    List.iter iter_session notebook#pages
  in
  let refresh_language lang =
    let lang = lang_manager#language lang in
    let iter_session v = v.script#source_buffer#set_language lang in
    List.iter iter_session notebook#pages
  in
  let refresh_toolbar b =
    if b then toolbar#misc#show () else toolbar#misc#hide ()
  in
  stick show_toolbar toolbar refresh_toolbar;
  let _ = source_style#connect#changed ~callback:refresh_style in
  let _ = source_language#connect#changed ~callback:refresh_language in

  (* Color configuration *)
  Tags.Script.incomplete#set_property
    (`BACKGROUND_STIPPLE
      (Gdk.Bitmap.create_from_data ~width:2 ~height:2 "\x01\x02"));

  (* Showtime ! *)
  w#show ()



(** {2 Coqide main function } *)

let make_file_buffer f =
  let f = if Filename.check_suffix f ".v" then f else f^".v" in
  FileAux.load_file ~maycreate:true f

let make_scratch_buffer () =
  let session = create_session None in
  let _ = notebook#append_term session in
  ()

let main files =
  build_ui ();
  reset_revert_timer ();
  reset_autosave_timer ();
  (match files with
    | [] -> make_scratch_buffer ()
    | _ -> List.iter make_file_buffer files);
  notebook#goto_page 0;
  MiscMenu.initial_about ();
  on_current_term (fun t -> t.script#misc#grab_focus ());
  Minilib.log "End of Coqide.main"


(** {2 Argument parsing } *)

(** By default, the coqtop we try to launch is exactly the current coqide
    full name, with the last occurrence of "coqide" replaced by "coqtop".
    This should correctly handle the ".opt", ".byte", ".exe" situations.
    If the replacement fails, we default to "coqtop", hoping it's somewhere
    in the path. Note that the -coqtop option to coqide overrides
    this default coqtop path *)

let read_coqide_args argv =
  let rec filter_coqtop coqtop project_files out = function
    |"-coqtop" :: prog :: args ->
      if coqtop = None then filter_coqtop (Some prog) project_files out args
      else (output_string stderr "Error: multiple -coqtop options"; exit 1)
    |"-f" :: file :: args ->
      if project_files <> None then
        (output_string stderr "Error: multiple -f options"; exit 1);
      let d = CUnix.canonical_path_name (Filename.dirname file) in
      let p = CoqProject_file.read_project_file file in
      filter_coqtop coqtop (Some (d,p)) out args
    |"-f" :: [] ->
      output_string stderr "Error: missing project file name"; exit 1
    |"-coqtop" :: [] ->
      output_string stderr "Error: missing argument after -coqtop"; exit 1
    |"-debug"::args ->
      Minilib.debug := true;
      Flags.debug := true;
      Backtrace.record_backtrace true;
      filter_coqtop coqtop project_files ("-debug"::out) args
    |"-coqtop-flags" :: flags :: args->
      Coq.ideslave_coqtop_flags := Some flags;
      filter_coqtop coqtop project_files out args
    |arg::args when out = [] && Minilib.is_prefix_of "-psn_" arg ->
      (* argument added by MacOS during .app launch *)
      filter_coqtop coqtop project_files out args
    |arg::args -> filter_coqtop coqtop project_files (arg::out) args
    |[] -> (coqtop,project_files,List.rev out)
  in
  let coqtop,project_files,argv = filter_coqtop None None [] argv in
  Ideutils.custom_coqtop := coqtop;
  custom_project_file := project_files;
  argv


(** {2 Signal handling } *)

(** The Ctrl-C (sigint) is handled as a interactive quit.
    For most of the other catchable signals we launch
    an emergency save of opened files and then exit. *)

let signals_to_crash =
  [Sys.sigabrt; Sys.sigalrm; Sys.sigfpe; Sys.sighup;
   Sys.sigill; Sys.sigpipe; Sys.sigquit; Sys.sigusr1; Sys.sigusr2]

let set_signal_handlers () =
  try
    Sys.set_signal Sys.sigint (Sys.Signal_handle File.quit);
    List.iter
      (fun i -> Sys.set_signal i (Sys.Signal_handle FileAux.crash_save))
      signals_to_crash
  with _ -> Minilib.log "Signal ignored (normal if Win32)"
