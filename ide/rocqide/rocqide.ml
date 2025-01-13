(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

(** The arguments that will be passed to rocqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
let custom_project_file = ref None
let sup_args = ref []

let logfile = ref None

(** {2 Notebook of sessions } *)

(** The main element of rocqide is a notebook of session views *)

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

let make_rocqtop_args fname =
  let open CoqProject_file in
  let base_args = match read_project#get with
    | Ignore_args -> !sup_args
    | Append_args -> !sup_args
    | Subst_args -> [] in
  let proj, args =
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
          Minilib.log ("About to read project file " ^ proj);
          let warning_fn x = Feedback.msg_warning Pp.(str x) in
          proj, coqtop_args_from_project (read_project_file ~warning_fn proj) @ base_args
  in
  let args = match fname with
    | None -> args
    | Some fname ->
      if List.exists (String.equal "-top") args then args
      else
        (* We basically copy the code of Names.check_valid since it is not exported *)
        (* to rocqide. This is to prevent a possible failure of parsing  "-topfile"  *)
        (* at initialization of rocqtop (see #10286) *)
        (* If the file name is a valid identifier, use it as toplevel name; *)
        (* otherwise the default “Top” will be used. *)
        try
          match Unicode.ident_refutation (Filename.chop_extension (Filename.basename fname)) with
          | Some _ -> args
          | None -> "-topfile"::fname::args
        with Invalid_argument _ ->
          failwith "RocqIDE cannot open files which do not have an extension in their filename."
  in
  proj, args

(** Setting drag & drop on widgets *)

let load_file_cb : (string -> unit) ref = ref ignore

let drop_received context ~x ~y data ~info ~time =
  if data#format = 8 then begin
    let files = Str.split (Str.regexp "\r?\n") data#data in
    List.iter (fun f ->
      let _, f = Glib.Convert.filename_from_uri f in
      !load_file_cb f;
    ) files;
    context#finish ~success:true ~del:false ~time
  end else context#finish ~success:false ~del:false ~time

let drop_targets = [
  { Gtk.target = "text/uri-list"; Gtk.flags = []; Gtk.info = 0 }
]

let set_drag (w : GObj.drag_ops) =
  w#dest_set drop_targets ~actions:[`COPY;`MOVE];
  w#connect#data_received ~callback:drop_received

(** Session management *)
let clear_db_highlight ?(retn=false) sn () =
  (match sn.debug_stop_pt with
    | Some (osn,bp,ep) ->
      if List.mem osn notebook#pages then  (* in case destroyed *)
        osn.script#clear_debugging_highlight bp ep;
      if retn then
        notebook#goto_term sn;
    | None -> ()
  )

let find_secondary_sn sn =
  let rec find = function
  | [] -> sn
  | hd :: tl ->
    (match hd.debug_stop_pt with
    | Some (osn,_,_) -> osn
    | None -> find tl)
  in find notebook#pages

let db_cmd sn cmd =
  ignore @@ RocqDriver.try_grab ~db:true sn.rocqtop
      (sn.rocqops#process_db_cmd cmd ~next:(function | _ -> RocqDriver.return ()))
      (fun () -> Minilib.log "Rocq busy, discarding db_cmd")

let forward_db_stack = ref ((fun _ -> failwith "forward_db_stack")
                     : session -> unit -> unit)
let forward_db_vars = ref ((fun _ -> failwith "forward_db_vars")
                     : session -> int -> unit)
let forward_highlight_code = ref ((fun _ -> failwith "forward_highlight_code")
                     : session -> string * int * int -> unit)
let forward_restore_bpts = ref ((fun _ -> failwith "forward_restore_bpts")
                     : session -> unit)
let forward_init_db = ref ((fun _ -> failwith "forward_init_db")
                     : session -> unit)

let create_session f =
  let project_file, args = make_rocqtop_args f in
  if project_file <> "" then
    flash_info (Printf.sprintf "Reading options from %s" project_file);
  let sn = Session.create f args in
  sn.debugger#set_forward_get_basename (fun _ -> sn.basename);
  RocqDriver.set_restore_bpts sn.rocqtop (fun _ -> !forward_restore_bpts sn);
  (sn.messages#route 0)#set_forward_send_db_cmd (db_cmd sn);
  (sn.messages#route 0)#set_forward_send_db_stack (!forward_db_stack sn);
  sn.debugger#set_forward_highlight_code (!forward_highlight_code sn);
  sn.debugger#set_forward_clear_db_highlight (clear_db_highlight sn);
  sn.debugger#set_forward_db_vars (!forward_db_vars sn);
  sn.rocqops#set_forward_clear_db_highlight (clear_db_highlight ~retn:true sn);
  sn.rocqops#set_forward_set_goals_of_dbg_session
    (fun msg ->
      sn.rocqops#set_debug_goal msg;
      sn.last_db_goals <- msg;
      let osn = (find_secondary_sn sn) in
      osn.rocqops#set_debug_goal msg;
      osn.last_db_goals <- msg);
  sn.rocqops#set_forward_init_db (fun () -> !forward_init_db sn);
  let _ = set_drag sn.script#drag in
  sn


let db_upd_bpts ?(next=RocqDriver.return) updates sn =
  if updates <> [] then
    ignore @@ RocqDriver.try_grab ~db:true sn.rocqtop
      (sn.rocqops#process_db_upd_bpts updates ~next:(function | _ -> next ()))
      (fun () -> Minilib.log "Rocq busy, discarding db_upd_bpts")

let get_updates sn =
  (* breakpoints in this buffer *)
  let upds = List.map (fun bp ->
      let start = sn.buffer#get_iter_at_mark (`NAME bp.mark_id) in
      let stop = start#forward_char in
      sn.buffer#apply_tag Tags.Script.breakpoint ~start ~stop; (* restore highlight for init *)
      (("ToplevelInput", bp.prev_byte_offset), true)
    ) sn.breakpoints
  in
  (* plus breakpoints in other buffers *)
  List.fold_left (fun upds osn ->
      match osn.abs_file_name with
      | _ when osn == sn -> upds
      | None -> upds
      | Some file ->
        (List.map (fun bp -> ((file, bp.prev_byte_offset), true)) osn.breakpoints) @ upds
    ) upds notebook#pages

(* init breakpoints for new session or re-init after reset *)
let init_bpts sn =
  RocqDriver.add_do_when_ready sn.rocqtop (fun _ ->
      let upds = get_updates sn in
      db_upd_bpts upds sn)

(* todo: shouldn't be so hard to chain operations *)
let () = forward_init_db := fun sn ->
  let updates = get_updates sn in
  let send_configd () =
    ignore @@ RocqDriver.try_grab ~db:true sn.rocqtop
      (sn.rocqops#process_db_configd () ~next:(function | _ -> RocqDriver.return ()))
      (fun () -> Minilib.log "Rocq busy, discarding db_configd")
  in
  if updates = [] then
    send_configd ()
  else
    db_upd_bpts updates sn ~next:(fun () -> send_configd (); RocqDriver.return ())

let restore_bpts sn =
  init_bpts sn;
  sn.debugger#set_stack [];
  sn.debugger#set_vars []

let _ = forward_restore_bpts := restore_bpts

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

let select_and_save ?parent ~saveas ?filename sn =
  let do_save = if saveas then sn.fileops#saveas ?parent else sn.fileops#save in
  let title = if saveas then "Save file as" else "Save file" in
  match select_file_for_save ~title ?parent ?filename () with
    |None -> false
    |Some f ->
      let ok = do_save f in
      confirm_save ok;
      if ok then begin
        sn.tab_label#set_text (Filename.remove_extension (Filename.basename f));
        sn.abs_file_name <- Some (Session.to_abs_file_name f);
        (* copying local breakpoints to other sessions seems pointless
           for a "save as" because the saved file needs to be compiled
           and other sessions restarted to use the new filename in
           breakpoints *)
      end;
      ok

let check_save ?parent ~saveas sn =
  try match sn.fileops#filename with
    |None -> select_and_save ?parent ~saveas sn
    |Some f ->
      let ok = sn.fileops#save f in
      confirm_save ok;
      ok
  with _ -> warning "Save Failed"; false

exception DontQuit

(* avoid getting 3 dialogs from ^C^C^C on the console.  You can still get 2 :-( *)
let in_quit_dialog = ref false

let check_quit ?parent saveall =
  in_quit_dialog := true;
  (try save_pref ()
   with e -> flash_info ("Cannot save preferences (" ^ Printexc.to_string e ^ ")"));
  let is_modified sn = sn.buffer#modified in
  if List.exists is_modified notebook#pages then begin
    let answ = Ui_dialogs.question_box ~title:"Quit"
      ~buttons:[ButtonWithLabel "Save named buffers and quit";
                ButtonWithLabel "Quit without saving";
                ButtonWithLabel "Don't quit"]
      ~default:0
      ~icon:(warn_image ())#coerce
      ?parent
      "There are unsaved buffers."
    in
    match answ with
      | 1 -> saveall ()
      | 2 -> ()
      | _ -> in_quit_dialog := false; raise DontQuit
  end;
  List.iter (fun sn -> RocqDriver.close_rocqtop sn.rocqtop) notebook#pages

(* For MacOS, just to be sure, we close all rocqtops (again?) *)
let close_and_quit () =
  List.iter (fun sn -> RocqDriver.close_rocqtop sn.rocqtop) notebook#pages;
  exit 0

(* Work around a deadlock due to OCaml exit cleanup. The standard [exit]
   function calls [flush_all], which can block if one of the opened channels is
   not valid anymore. We do not register [at_exit] functions in RocqIDE, so
   instead of flushing we simply die as gracefully as possible in the function
   below. *)
external sys_exit : int -> 'a = "caml_sys_exit"

let crash_save exitcode =
  Minilib.log "Starting emergency save of buffers in .crashrocqide files";
  let idx =
    let r = ref 0 in
    fun () -> incr r; string_of_int !r
  in
  let save_session sn =
    let filename = match sn.fileops#filename with
      | None -> "Unnamed_rocqscript_" ^ idx () ^ ".crashrocqide"
      | Some f -> f^".crashrocqide"
    in
    try
      if try_export filename (sn.buffer#get_text ()) then
        Minilib.log ("Saved "^filename)
      else Minilib.log ("Could not save "^filename)
    with _ -> Minilib.log ("Could not save "^filename)
  in
  List.iter save_session notebook#pages;
  Minilib.log "End emergency save";
  sys_exit exitcode

end

let () = load_file_cb := (fun s -> FileAux.load_file s)

let clear_all_bpts sn =
  sn.breakpoints <- [];
  init_bpts sn

(** Callbacks for the File menu *)

module File = struct

let newfile _ =
  let sn = create_session None in
  let index = notebook#append_term sn in
  notebook#goto_page index;
  init_bpts sn

let load ?parent _ =
  let filename =
    try notebook#current_term.fileops#filename
    with Invalid_argument _ -> None in
  let filenames = select_file_for_open ~title:"Load file" ~multiple:true ?parent ?filename () in
  List.iter FileAux.load_file filenames;
  on_current_term (fun sn -> init_bpts sn)

let save ?parent _ = on_current_term (FileAux.check_save ?parent ~saveas:false)

let saveas ?parent sn =
  try
    let filename = sn.fileops#filename in
    ignore (FileAux.select_and_save ?parent ~saveas:true ?filename sn);
    (* if a new file, adds breakpoints from other files into this session *)
    init_bpts sn
  with _ -> warning "Save Failed"

let saveas ?parent = cb_on_current_term (saveas ?parent)

let saveall _ =
  List.iter
    (fun sn -> match sn.fileops#filename with
      | None -> ()
      | Some f -> ignore (sn.fileops#save f))
    notebook#pages

let () = RocqDriver.save_all := saveall

let reload_all ?parent _ =
  List.iter
    (fun sn -> if sn.fileops#changed_on_disk then begin
        clear_all_bpts sn;
        sn.fileops#reload ?parent ()
      end)
    notebook#pages

let win_interrupt = ref false

let quit ?parent _ =
  if !win_interrupt then
    win_interrupt := false
  else if not !FileAux.in_quit_dialog then
    try FileAux.check_quit ?parent saveall; exit 0
    with FileAux.DontQuit -> ()

let close_buffer ?parent sn =
  let do_remove () =
    notebook#remove_page notebook#current_page;
    (* remove breakpoints in this buffer from other sessions *)
    if sn.breakpoints <> [] then
      match sn.abs_file_name with
      | None -> ()
      | Some file ->
        List.iter (fun osn ->
            if sn != osn then begin
              let upds = List.fold_left (fun upds bp ->
                  ((file, bp.prev_byte_offset), false) :: upds)
                [] sn.breakpoints in
              RocqDriver.add_do_when_ready osn.rocqtop (fun _ -> db_upd_bpts upds osn)
            end
          ) notebook#pages
  in
  if not sn.buffer#modified then do_remove ()
  else
    let answ = Ui_dialogs.question_box ~title:"Close"
      ~buttons:[ButtonWithLabel "Save buffer and close";
                ButtonWithLabel "Close without saving";
                ButtonWithLabel "Don't close"]
      ~default:0
      ~icon:(warn_image ())#coerce
      ?parent
      "This buffer has unsaved modifications"
    in
    match answ with
      | 1 when FileAux.check_save ?parent ~saveas:true sn -> do_remove ()
      | 2 -> do_remove ()
      | _ -> ()

let close_buffer ?parent = cb_on_current_term (close_buffer ?parent)

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
        local_cd f ^ cmd_rocqdoc#get ^ " --" ^ kind ^ " -o " ^
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
        local_cd f_name ^ cmd_rocqdoc#get ^ " -ps " ^
        Filename.quote (Filename.basename f_name) ^ " | " ^ cmd_print#get
      in
      let w = GWindow.window ~title:"Print" ~modal:true
        ~position:`CENTER ~wmclass:("RocqIDE","RocqIDE") ()
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

let reset_reload_timer () =
  FileOps.reload_timer.kill ();
  if global_auto_reload#get then
    FileOps.reload_timer.run
      ~ms:global_auto_reload_delay#get
      ~callback:(fun () -> File.reload_all (); true)

let reset_autosave_timer () =
  let autosave sn = try sn.fileops#auto_save with _ -> () in
  let autosave_all () = List.iter autosave notebook#pages; true in
  FileOps.autosave_timer.kill ();
  if auto_save#get then
    FileOps.autosave_timer.run ~ms:auto_save_delay#get ~callback:autosave_all

(** Export of functions used in [rocqide_main] : *)

let close_and_quit = FileAux.close_and_quit
let crash_save = FileAux.crash_save
let do_load f = FileAux.load_file f

(** Callbacks for external commands *)

module External = struct

let rocq_makefile sn =
  match sn.fileops#filename with
    |None -> flash_info "Cannot make makefile: this buffer has no name"
    |Some f ->
      let cmd = local_cd f ^ cmd_rocqmakefile#get in
      let finally st = flash_info (cmd_rocqmakefile#get ^ pr_exit_status st)
      in
      run_command ignore finally cmd

let rocq_makefile = cb_on_current_term rocq_makefile

let editor ?parent sn =
  match sn.fileops#filename with
    |None -> warning "Call to external editor available only on named files"
    |Some f ->
      File.save ();
      let f = Filename.quote f in
      let cmd = Util.subst_command_placeholder cmd_editor#get f in
      run_command ignore (fun _ -> sn.fileops#reload ?parent ()) cmd

let editor ?parent = cb_on_current_term (editor ?parent)

let compile sn =
  File.save ();
  match sn.fileops#filename with
    |None -> flash_info "Active buffer has no name"
    |Some f ->
      let args = RocqDriver.get_arguments sn.rocqtop in
      let cmd = cmd_rocqc#get
        ^ " " ^ String.concat " " (List.map Filename.quote args)
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
          sn.messages#default_route#set (Pp.str ("Compilation output:\n" ^ cmd ^ "\n"));
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
    let starti = Ideutils.get_iter_at_byte b ~line:(line-1) start in
    let stopi = Ideutils.get_iter_at_byte b ~line:(line-1) stop in
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
  | Interface.Fail x -> sn.rocqops#handle_failure x
  | Interface.Good status ->
    let path = match status.Interface.status_path with
      | [] | _ :: [] -> "" (* Drop the topmost level, usually "Top" *)
      | _ :: l -> " in " ^ String.concat "." l
    in
    let name = match status.Interface.status_proofname with
      | None -> ""
      | Some n -> ", proving " ^ n
    in
    display ("Ready"^ (if microPG#get then ", [μPG]" else "") ^ path ^ name);
    RocqDriver.return ()
  in
  RocqDriver.bind (RocqDriver.status false) next

let find_next_occurrence ~backward sn =
  (* go to the next occurrence of the current word, forward or backward *)
  let b = sn.buffer in
  let start = find_word_start (b#get_iter_at_mark `INSERT) in
  let stop = find_word_end start in
  let text = b#get_text ~start ~stop () in
  let search = if backward then start#backward_search else stop#forward_search
  in
  match search text with
    |None -> ()
    |Some(where, _) -> b#place_cursor ~where; sn.script#recenter_insert

let send_to_rocq_aux f sn =
  let info () = Minilib.log "Rocq busy, discarding query" in
  let f = RocqDriver.seq (f sn) (update_status sn) in
  ignore @@ RocqDriver.try_grab sn.rocqtop f info

let send_to_rocq f = on_current_term (send_to_rocq_aux f)

let db_continue opt sn =
  RocqDriver.try_grab ~db:true sn.rocqtop (sn.rocqops#process_db_continue opt
    ~next:(function | _ -> RocqDriver.return ()))
    (fun () -> Minilib.log "Rocq busy, discarding db_continue")

(* find the session identified by sid.  If not specified and the current term
   is the stopping point for another session, direct actions to that term *)
let find_db_sn ?sid () =
  let cur = notebook#current_term in
  let f = match sid with
  | Some sid -> fun term -> term.sid == sid
  | None -> fun term ->
    match term.debug_stop_pt with
    | Some (osn,_,_) -> osn == cur
    | None -> false
  in
  let res = List.filter f notebook#pages in
  if res = [] then cur else List.hd res

let resume_debugger ?sid opt =
  let term = try Some (find_db_sn ?sid ()) with Invalid_argument _ -> None in
  match term with
  | None -> false
  | Some t ->
    if RocqDriver.is_stopped_in_debugger t.rocqtop && db_continue opt t then begin
      RocqDriver.set_stopped_in_debugger t.rocqtop false;
      clear_db_highlight t ();
      t.debugger#set_stack [];
      t.debugger#set_vars [];
      t.messages#default_route#set_editable2 false;
      t.messages#default_route#push Feedback.Notice (Pp.mt ());
      (* Ideutils.push_info "Rocq is computing";  todo: needs to be per-session *)
      true
    end else false

(* figure out which breakpoint locations have changed because the script was edited *)
let calculate_bpt_updates () =
  let fn = "ToplevelInput" in
  let rec update_bpts sn upd bpts_res = function
    | bp :: tl ->
      let iter = sn.buffer#get_iter_at_mark (`NAME bp.mark_id) in
      let has_tag = iter#has_tag Tags.Script.breakpoint in
      let prev_byte_offset = bp.prev_byte_offset in
      if not has_tag then begin
        sn.buffer#delete_mark (`NAME bp.mark_id); (* remove *)
        update_bpts sn (((fn, prev_byte_offset), false) :: upd) bpts_res tl
      end else if iter#offset <> bp.prev_uni_offset then begin
        bp.prev_uni_offset <- iter#offset;        (* move *)
        let byte_offset = Ideutils.buffer_off_to_byte_off sn.buffer iter#offset in
        bp.prev_byte_offset <- byte_offset;
        update_bpts sn (((fn, byte_offset), true)
            :: ((fn, prev_byte_offset), false) :: upd)
          (bp :: bpts_res) tl (* move *)
      end else
        update_bpts sn upd (bp :: bpts_res) tl       (* no change, keep *)
    | [] -> (List.rev upd, List.rev bpts_res)  (* order matters *)
  in
  let upds = List.map (fun sn -> update_bpts sn [] [] sn.breakpoints) notebook#pages in
  upds

let maybe_update_breakpoints () =
  let upds = calculate_bpt_updates () in
  List.iter2 (fun sn (_, bpts) ->
      sn.breakpoints <- bpts;
      let sn_upds = List.concat (List.mapi (fun n sn2 ->
        let (upd, _) = List.nth upds n in
        match sn2.abs_file_name with
          | _ when sn == sn2 -> upd (* as TopLevelInput *)
          | Some fn ->
            List.map (fun ((_, off), set) -> ((fn, off), set)) upd
          | None -> []
        ) notebook#pages) in
      if sn_upds <> [] then
        RocqDriver.add_do_when_ready sn.rocqtop (fun _ -> db_upd_bpts sn_upds sn)
    ) notebook#pages upds

module Nav = struct
  let forward_one_sid ?sid _ =
    maybe_update_breakpoints ();
    if not (resume_debugger ?sid Interface.StepOver) then
      send_to_rocq (fun sn -> sn.rocqops#process_next_phrase)
  let forward_one x = forward_one_sid x
  let continue ?sid _ = maybe_update_breakpoints ();
    if not (resume_debugger ?sid Interface.Continue) then
      send_to_rocq (fun sn -> sn.rocqops#process_until_end_or_error)
  let step_in ?sid _ = maybe_update_breakpoints ();
    if not (resume_debugger ?sid Interface.StepIn) then
      send_to_rocq (fun sn -> sn.rocqops#process_next_phrase)
  let step_out ?sid _ = maybe_update_breakpoints ();
    if not (resume_debugger ?sid Interface.StepOut) then
      send_to_rocq (fun sn -> sn.rocqops#process_next_phrase)
  let backward_one _ = maybe_update_breakpoints ();
    send_to_rocq (fun sn -> init_bpts sn; sn.rocqops#backtrack_last_phrase)
  let run_to_cursor _ = maybe_update_breakpoints ();
    send_to_rocq (fun sn -> sn.rocqops#go_to_insert)
  let run_to_end _ = maybe_update_breakpoints ();
    send_to_rocq (fun sn -> sn.rocqops#process_until_end_or_error)
  let previous_occ = cb_on_current_term (find_next_occurrence ~backward:true)
  let next_occ = cb_on_current_term (find_next_occurrence ~backward:false)
  let restart _ =
    Minilib.log "Reset Initial";
    maybe_update_breakpoints ();
    if notebook#pages <> [] then begin
      let sn = notebook#current_term in
      RocqDriver.reset_rocqtop sn.rocqtop (* calls init_bpts *)
    end
  let interrupt _ =  (* terminate computation *)
    if Sys.os_type = "Win32" then File.win_interrupt := true;
    Minilib.log "User interrupt received";
    if not (resume_debugger Interface.Interrupt) && notebook#pages <> [] then begin
      let osn = (find_db_sn ()) in
      RocqDriver.interrupt_rocqtop osn.rocqtop CString.(Set.elements (Map.domain osn.jobpage#data))
    end
  let break ?sid _ =  (* stop at the next possible stopping point *)
    if notebook#pages <> [] then begin
      let orocqtop = (find_db_sn ?sid ()).rocqtop in
      if not (RocqDriver.is_stopped_in_debugger orocqtop) then
        RocqDriver.send_break orocqtop
    end
  let show_debugger _ =
    on_current_term (fun sn -> sn.debugger#show ())
  let join_document _ = send_to_rocq (fun sn -> sn.rocqops#join_document)
end

let f9       = GtkData.AccelGroup.parse "F9"
let f10      = GtkData.AccelGroup.parse "F10"
let f11      = GtkData.AccelGroup.parse "F11"
let shft_f10 = GtkData.AccelGroup.parse "<Shift>F10"
let ctl_up   = GtkData.AccelGroup.parse "<Ctrl>Up"
let ctl_down = GtkData.AccelGroup.parse "<Ctrl>Down"

(* handle certain function keys from detached Messages panel
   functions are directed to the specified session or the
   current session, not the Messages session (debatable) *)
let forward_keystroke key sid =
  if      key = f9 then (Nav.continue ~sid (); true)
  else if key = f10 then (Nav.step_in ~sid (); true)
  else if key = f11 then (Nav.break ~sid (); true)
  else if key = shft_f10 then (Nav.step_out ~sid (); true)
  else if key = ctl_up then (Nav.backward_one (*~sid*) (); true)
  else if key = ctl_down then (Nav.forward_one_sid ~sid (); true)
  else false

let _ = Wg_MessageView.forward_keystroke := forward_keystroke
let _ = Wg_Debugger.forward_keystroke := forward_keystroke

let printopts_callback opts v =
  let b = v#get_active in
  let () = List.iter (fun o -> RocqDriver.PrintOpt.set o b) opts in
  send_to_rocq (fun sn -> sn.rocqops#show_goals)

(** Templates menu *)

let get_current_word term =
  (* First look to find if autocompleting *)
  match term.script#proposal with
  | Some p -> p
  | None ->
  (* Then look at the current selected word *)
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
  (* Otherwise try to find the word around the cursor *)
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
    flash_info "Not an inductive type"; RocqDriver.return ()
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
    RocqDriver.return ()

let match_callback sn =
  let w = get_current_word sn in
  let rocqtop = sn.rocqtop in
  let query = RocqDriver.bind (RocqDriver.mkcases w) (display_match sn) in
  ignore @@ RocqDriver.try_grab rocqtop query
    (fun () -> Minilib.log "Rocq busy, discarding mkcases")

let match_callback = cb_on_current_term match_callback

(** Queries *)

module Query = struct

let doquery query sn =
  sn.messages#default_route#clear;
  ignore @@ RocqDriver.try_grab sn.rocqtop (sn.rocqops#raw_rocq_query query ~route_id:0
    ~next:(function
        | Interface.Fail (_, _, err) ->
            let err = Ideutils.validate err in
            sn.messages#default_route#add err;
            RocqDriver.return ()
        | Interface.Good () -> RocqDriver.return ()))
    (fun () -> Minilib.log "Rocq busy, discarding raw_rocq_query")

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
    "Welcome to RocqIDE, an Integrated Development Environment for Rocq"
  in
  let rocq_version = RocqDriver.short_version () in
  let version_info =
    if Glib.Utf8.validate rocq_version then
      "\nYou are running " ^ rocq_version
    else ""
  in
  let msg = initial_string ^ version_info ^ log_file_message () in
  on_current_term (fun term -> term.messages#default_route#add_string msg)

let rocq_icon () =
  (* May raise Nof_found *)
  let name = "coq.png" in
  let chk d = Sys.file_exists (Filename.concat d name) in
  let dir = List.find chk (Minilib.rocqide_data_dirs ()) in
  Filename.concat dir name

let show_proof_diff where sn =
  sn.messages#default_route#clear;
  ignore @@ RocqDriver.try_grab sn.rocqtop (sn.rocqops#proof_diff where
    ~next:(function
        | Interface.Fail (_, _, err) ->
            let err = if (Pp.string_of_ppcmds err) <> "No proofs to diff." then err else
              Pp.str "Put the cursor over proven lines for \"Show Proof\" diffs"
            in
            let err = Ideutils.validate err in
            sn.messages#default_route#add err;
            RocqDriver.return ()
        | Interface.Good diff ->
            sn.messages#default_route#add diff;
            RocqDriver.return ()))
      (fun () -> Minilib.log "Rocq busy, discarding raw_rocq_query")

let show_proof_diffs _ = cb_on_current_term (show_proof_diff `INSERT) ()

let highlight_code sn loc =
  let (file, bp, ep) = loc in
  let highlight () =
    clear_db_highlight sn ();
    notebook#current_term.script#set_debugging_highlight bp ep;
    sn.debug_stop_pt <- Some (notebook#current_term, bp, ep);
    (* also show goal in secondary script goal panel *)
    notebook#current_term.rocqops#set_debug_goal sn.last_db_goals
  in
  if file = "ToplevelInput" then begin
    notebook#goto_term sn;
    highlight ()
  end else if CString.is_suffix ".v" file then begin
    try let _ = Unix.stat file in
      FileAux.load_file file;
      highlight ()
    with Unix.Unix_error (Unix.ENOENT,_,_) ->
      (* or just show in messages panel? *)
      let title = "Warning" in
      let icon = (warn_image ())#coerce in
      let buttons = ["OK"] in
      let msg = Printf.sprintf "Can't find: %s" file in
      let _ = GToolbox.question_box ~title ~buttons ~icon msg in
      ()
  end

let _ = forward_highlight_code := highlight_code

let db_stack sn _ =
  RocqDriver.add_do_when_ready sn.rocqtop (fun _ ->
    ignore @@ RocqDriver.try_grab ~db:true sn.rocqtop (sn.rocqops#process_db_stack
      ~next:(function
          | Interface.Good stack ->
            sn.debugger#set_stack stack;
            RocqDriver.return ()
          | Interface.Fail _ ->
            RocqDriver.return ()
          ))
      (fun () -> Minilib.log "Rocq busy, discarding db_stack")
  )

let _ = forward_db_stack := db_stack

let db_vars sn line =
  RocqDriver.add_do_when_ready sn.rocqtop (fun _ ->
    ignore @@ RocqDriver.try_grab ~db:true sn.rocqtop (sn.rocqops#process_db_vars line
      ~next:(function
          | Interface.Good vars ->
            sn.debugger#set_vars vars;
            RocqDriver.return ()
          | Interface.Fail _ ->
            RocqDriver.return ()
          ))
      (fun () -> Minilib.log "Rocq busy, discarding db_vars")
  )

let _ = forward_db_vars := db_vars

let next_bpt = ref 0

let compute_toggle sn =
  let start = sn.buffer#get_iter_at_mark `INSERT in
  let stop = start#forward_char in
  let file = "ToplevelInput" in
  let prev_uni_offset = start#offset in
  let prev_byte_offset = Ideutils.buffer_off_to_byte_off sn.buffer prev_uni_offset in
  let rec update_bpts = function
    | bp :: tl ->
      let iter = sn.buffer#get_iter_at_mark (`NAME bp.mark_id) in
      if iter#offset = prev_uni_offset then begin
        sn.buffer#remove_tag Tags.Script.breakpoint ~start ~stop;
        sn.buffer#delete_mark (`NAME bp.mark_id);
        [((file, prev_byte_offset), false)],
        List.filter (fun x ->
            x.mark_id <> bp.mark_id
          ) sn.breakpoints
      end else
        update_bpts tl
    | [] ->
      sn.buffer#apply_tag Tags.Script.breakpoint ~start ~stop;
      incr next_bpt;
      let mark_id = "bp" ^ (string_of_int !next_bpt) in
      let _ = sn.buffer#create_mark ~name:mark_id start in
      ([((file, prev_byte_offset), true)], ({ mark_id; prev_byte_offset; prev_uni_offset }
          :: sn.breakpoints))
  in
  let upd, bpts_res = update_bpts sn.breakpoints in
  sn.breakpoints <- List.rev bpts_res;
  upd

let toggle_breakpoint_i sn =
  maybe_update_breakpoints ();
  let upd = compute_toggle sn in
  db_upd_bpts upd sn;
  (* if this session has an associated file, toggle bp in all other sessions *)
  match sn.abs_file_name with
  | Some fname ->
    let upd2 = List.map (fun bp ->
        let ((_, off), toggle) = bp in
        ((fname, off), toggle)
      ) upd in
    List.iter (fun osn ->
        if osn != sn then
          RocqDriver.add_do_when_ready osn.rocqtop (fun _ -> db_upd_bpts upd2 osn)
      ) notebook#pages
  | None -> ()

let all_sessions_ready _ =
  List.fold_left (fun rdy sn -> rdy && RocqDriver.is_ready_or_stopped_in_debugger sn.rocqtop)
      true notebook#pages

let toggle_breakpoint _ =
  if all_sessions_ready () then
    on_current_term toggle_breakpoint_i

let about _ =
  let dialog = GWindow.about_dialog () in
  let _ = dialog#connect#response ~callback:(fun _ -> dialog#destroy ()) in
  let _ =
    try dialog#set_logo (GdkPixbuf.from_file (rocq_icon ()))
    with _ -> ()
  in
  let copyright =
    "Rocq is developed by the Rocq Development Team\n\
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
  dialog#set_name "RocqIDE";
  dialog#set_comments "The Rocq Integrated Development Environment";
  dialog#set_website Coq_config.wwwcoq;
  dialog#set_version Coq_config.version;
  dialog#set_copyright copyright;
  dialog#set_authors authors;
  dialog#show ()

let apply_unicode_binding =
  cb_on_current_term (fun t ->
    t.script#apply_unicode_binding())

let rocqtop_arguments sn =
  init_bpts sn;
  let dialog = GWindow.dialog ~title:"Coqtop arguments" () in
  let rocqtop = sn.rocqtop in
  (* Text entry *)
  let text = Ideutils.encode_string_list (RocqDriver.get_arguments rocqtop) in
  let entry = GEdit.entry ~text ~packing:dialog#vbox#add () in
  (* Buttons *)
  let box = dialog#action_area in
  let ok = GButton.button ~stock:`OK ~packing:box#add () in
  let fail s =
    let msg = Printf.sprintf "Invalid arguments: %s" s in
    let () = sn.messages#default_route#clear in
    sn.messages#default_route#push Feedback.Error (Pp.str msg) in
  let ok_cb () =
    let ntext = entry#text in
    if ntext <> text then
      match try Util.Inr (Ideutils.decode_string_list ntext) with Failure s -> Util.Inl s with
      | Util.Inl s -> fail s
      | Util.Inr nargs ->
      let failed = RocqDriver.filter_rocq_opts nargs in
      match failed with
      | [] ->
        let () = RocqDriver.set_arguments rocqtop nargs in
        dialog#destroy ()
      | args ->
        fail (String.concat " " args)
    else dialog#destroy ()
  in
  let _ = entry#connect#activate ~callback:ok_cb in
  let _ = ok#connect#clicked ~callback:ok_cb in
  let cancel = GButton.button ~stock:`CANCEL ~packing:box#add () in
  let cancel_cb () = dialog#destroy () in
  let _ = cancel#connect#clicked ~callback:cancel_cb in
  dialog#show ()

let rocqtop_arguments = cb_on_current_term rocqtop_arguments

let show_hide_query_pane sn =
  let ccw = sn.command in
  if ccw#visible then ccw#hide else ccw#show

let zoom_fit sn =
  let script = sn.script in
  let space = script#misc#allocation.Gtk.width in
  let cols = script#right_margin_position in
  let pango_ctx = script#misc#pango_context in
  let layout = pango_ctx#create_layout#as_layout in
  Pango.Layout.set_text layout (String.make cols 'X');
  let tlen = fst (Pango.Layout.get_pixel_size layout) in
  let ft = Pango.Font.from_string text_font#get in
  let fsize = Pango.Font.get_size ft in
  Pango.Font.set_size ft (fsize * space / tlen / Pango.scale * Pango.scale);
  text_font#set (Pango.Font.to_string ft);
  save_pref ()

end

(** Refresh functions *)

let refresh_notebook_pos () =
  let pos = match document_tabs_pos#get with
    | "left" -> `LEFT
    | "right" -> `RIGHT
    | "bottom" -> `BOTTOM
    | _ -> `TOP
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

module Opt = RocqDriver.PrintOpt

let printopts_items menu_name l =
  let f Opt.{ label; init; opts } =
    let k, name = get_shortcut label in
    let accel = Option.map ((^) modifier_for_display#get) k in
    printopts_item_names := name :: !printopts_item_names;
    toggle_item name ~label ?accel ~active:init
      ~callback:(printopts_callback opts)
      menu_name
  in
  List.iter f l

let no_under = Util.String.map (fun x -> if x = '_' then '-' else x)

(** Create alphabetical menu items with elements in sub-items.
    [l] is a list of lists, one per initial letter *)

let alpha_items menu_name item_name l =
  let mk_item text =
    let text' =
      let len = String.length text in
      let buf = Buffer.create (len + 1) in
      let escaped = ref false in
      String.iter (fun c ->
          if !escaped then
            let () = Buffer.add_char buf c in
            escaped := false
          else if c = '_' then escaped := true
          else Buffer.add_char buf c
        ) text;
      if text.[len - 1] = '.'
      then Buffer.add_char buf '\n'
      else Buffer.add_char buf ' ';
      Buffer.contents buf
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

(** {2 Creation of the main rocqide window } *)

let build_ui () =
  (* issue 12779 *)
  GtkData.StyleContext.add_provider_for_screen
    (Gdk.Screen.default ())
    begin
      let provider = GObj.css_provider () in
      provider#load_from_data "button { box-shadow: none }";
      provider#as_css_provider
    end
    GtkData.StyleContext.ProviderPriority.application;

  let w = GWindow.window
    ~wmclass:("RocqIDE","RocqIDE")
    ~width:window_width#get ~height:window_height#get
    ~title:"RocqIDE" ()
  in
  let () =
    try w#set_icon (Some (GdkPixbuf.from_file (MiscMenu.rocq_icon ())))
    with _ -> ()
  in
  let _ = w#event#connect#delete ~callback:(fun _ -> File.quit ~parent:w (); true) in
  let _ = w#misc#connect#size_allocate
            ~callback:(fun rect -> window_size := (rect.Gtk.width, rect.Gtk.height)) in
  let _ = set_drag w#drag in

  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  let file_menu = GAction.action_group ~name:"File" () in
  let edit_menu = GAction.action_group ~name:"Edit" () in
  let view_menu = GAction.action_group ~name:"View" () in
  let export_menu = GAction.action_group ~name:"Export" () in
  let navigation_menu = GAction.action_group ~name:"Navigation" () in
  let templates_menu = GAction.action_group ~name:"Templates" () in
  let tools_menu = GAction.action_group ~name:"Tools" () in
  let queries_menu = GAction.action_group ~name:"Queries" () in
  let compile_menu = GAction.action_group ~name:"Compile" () in
  let debug_menu = GAction.action_group ~name:"Debug" () in
  let windows_menu = GAction.action_group ~name:"Windows" () in
  let help_menu = GAction.action_group ~name:"Help" () in
  let all_menus = [
    file_menu; edit_menu; view_menu; export_menu; navigation_menu;
    templates_menu; tools_menu; queries_menu; compile_menu; debug_menu; windows_menu;
    help_menu; ] in

  menu file_menu [
    item "File" ~label:"_File";
    item "New" ~callback:File.newfile ~stock:`NEW;
    item "Open" ~callback:(File.load ~parent:w) ~stock:`OPEN ~tooltip:"Open file";
    item "Save" ~callback:(File.save ~parent:w) ~stock:`SAVE ~tooltip:"Save current buffer";
    item "Save as" ~stock:`SAVE_AS ~callback:(File.saveas ~parent:w);
    item "Save all" ~label:"Sa_ve all" ~callback:File.saveall;
    item "Close buffer" ~label:"_Close buffer" ~stock:`CLOSE
      ~callback:(File.close_buffer ~parent:w) ~tooltip:"Close current buffer";
    item "Print..." ~label:"_Print..." ~accel:"<Primary>p"
      ~callback:File.print ~stock:`PRINT;
    item "Rehighlight" ~label:"Re_highlight" ~accel:"<Primary>l"
      ~callback:File.highlight ~stock:`REFRESH;
    item "Quit" ~stock:`QUIT ~callback:(File.quit ~parent:w);
  ];

  menu export_menu [
    item "Export to" ~label:"E_xport to";
    item "Html" ~label:"_HTML" ~callback:(File.export "html");
    item "Latex" ~label:"_LaTeX" ~callback:(File.export "latex");
    item "Dvi" ~label:"_DVI" ~callback:(File.export "dvi");
    item "Pdf" ~label:"_PDF" ~callback:(File.export "pdf");
    item "Ps" ~label:"P_ostScript" ~callback:(File.export "ps");
  ];

  menu edit_menu [
    item "Edit" ~label:"_Edit";
    item "Undo" ~accel:"<Primary>z" ~stock:`UNDO
      ~callback:(cb_on_current_term (fun t -> t.script#undo ()));
    item "Redo" ~accel:"<Primary><Shift>z" ~stock:`REDO
      ~callback:(cb_on_current_term (fun t -> t.script#redo ()));
    item "Select All" ~accel:"<Primary>a" ~stock:`SELECT_ALL
      ~callback:(cb_on_current_term (fun t ->
         t.script#select_all ();
         t.proof#select_all ();
         t.messages#select_all ();
         t.debugger#select_all ()));
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
      ~callback:(External.editor ~parent:w);
    item "Preferences" ~accel:"<Primary>comma" ~stock:`PREFERENCES
      ~callback:(fun _ ->
        begin
          try Preferences_ui.configure ~apply:refresh_notebook_pos w
          with e ->
            flash_info ("Editing preferences failed (" ^ Printexc.to_string e ^ ")")
        end;
        reset_reload_timer ());
  ];

  menu view_menu [
    item "View" ~label:"_View";
    item "Previous tab" ~label:"_Previous tab" ~accel:"<Primary>Page_Up"
      ~stock:`GO_BACK
      ~callback:(fun _ -> notebook#previous_page ());
    item "Next tab" ~label:"_Next tab" ~accel:"<Primary>Page_Down"
      ~stock:`GO_FORWARD
      ~callback:(fun _ -> notebook#next_page ());
    item "Zoom in" ~accel:("<Primary>plus")
        ~stock:`ZOOM_IN ~callback:(fun _ ->
          let ft = Pango.Font.from_string text_font#get in
          Pango.Font.set_size ft (Pango.Font.get_size ft + Pango.scale);
          text_font#set (Pango.Font.to_string ft);
          save_pref ());
    item "Zoom out" ~accel:("<Primary>minus")
        ~stock:`ZOOM_OUT ~callback:(fun _ ->
          let ft = Pango.Font.from_string text_font#get in
          Pango.Font.set_size ft (Pango.Font.get_size ft - Pango.scale);
          text_font#set (Pango.Font.to_string ft);
          save_pref ());
    item "Zoom fit" ~accel:("<Primary>0")
        ~stock:`ZOOM_FIT ~callback:(cb_on_current_term MiscMenu.zoom_fit);
    toggle_item "Show Toolbar" ~label:"Show _Toolbar"
      ~active:(show_toolbar#get)
      ~callback:(fun _ -> show_toolbar#set (not show_toolbar#get));
    item "Query Pane" ~label:"_Query Pane" ~accel:"F2"
      ~callback:(cb_on_current_term MiscMenu.show_hide_query_pane);
    GAction.group_radio_actions
      ~init_value:(
        let v = diffs#get in
        List.iter (fun o -> Opt.set o v) Opt.diff_item.Opt.opts;
        match v with "on" -> 1 | "removed" -> 2 | _ -> 0)
      ~callback:begin fun n ->
        (match n with
        | 0 -> List.iter (fun o -> Opt.set o "off"; diffs#set "off") Opt.diff_item.Opt.opts
        | 1 -> List.iter (fun o -> Opt.set o "on"; diffs#set "on") Opt.diff_item.Opt.opts
        | 2 -> List.iter (fun o -> Opt.set o "removed"; diffs#set "removed") Opt.diff_item.Opt.opts
        | _ -> assert false);
        send_to_rocq (fun sn -> sn.rocqops#show_goals)
        end
      [
        radio "Unset diff" 0 ~label:"_Don't show diffs";
        radio "Set diff" 1 ~label:"Show diffs: only _added";
        radio "Set removed diff" 2 ~label:"Show diffs: added and _removed";
      ];
    item "Show Proof Diffs" ~label:"_Show Proof (with diffs, if set)" ~accel:"<Shift>F2"
      ~callback:MiscMenu.show_proof_diffs;
  ];
  printopts_items view_menu RocqDriver.PrintOpt.bool_items;

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
    ("Run to cursor", "Run to _cursor", `JUMP_TO, Nav.run_to_cursor, "Run to cursor", "Right");
    ("Reset", "_Reset", `GOTO_TOP, Nav.restart, "Reset Rocq", "Home");
    ("Run to end", "_Run to end", `GOTO_BOTTOM, Nav.run_to_end, "Run to end", "End");
    ("Fully check", "_Fully check", `EXECUTE, Nav.join_document, "Fully check the document", "Return");
    ("Interrupt", "_Interrupt", `STOP, Nav.interrupt, "Interrupt computations", "Break");
    (* wait for this available in GtkSourceView !
    ("Hide", "_Hide", `MISSING_IMAGE,
        ~callback:(fun _ -> let sess = notebook#current_term in
          toggle_proof_visibility sess.buffer sess.analyzed_view#get_insert), "Hide proof", "h"); *)
    ("Previous", "_Previous occurrence", `GO_BACK, Nav.previous_occ,
        "Previous occurrence of word under cursor", "less");
    ("Next", "_Next occurrence", `GO_FORWARD, Nav.next_occ,
        "Next occurrence of word under cursor", "greater");
  ] end;

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
  alpha_items templates_menu "Template" Rocq_commands.commands;

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
    item "Comment" ~label:"_Comment" ~accel:"<Primary>D"
      ~callback:(cb_on_current_term (fun t -> t.script#comment ()));
    item "Uncomment" ~label:"_Uncomment" ~accel:"<Primary><Shift>D"
      ~callback:(cb_on_current_term (fun t -> t.script#uncomment ()));
    item "Coqtop arguments" ~label:"Coqtop _arguments"
      ~callback:MiscMenu.rocqtop_arguments;
    item "LaTeX-to-unicode" ~label:"_LaTeX-to-unicode" ~accel:"<Shift>space"
      ~callback:MiscMenu.apply_unicode_binding;
  ];

  menu compile_menu [
    item "Compile" ~label:"_Compile";
    item "Compile buffer" ~label:"_Compile buffer" ~callback:External.compile;
    item "Make" ~label:"_Make" ~accel:"F6"
      ~callback:External.make;
    item "Next error" ~label:"_Next error" ~accel:"F7"
      ~callback:External.next_error;
    item "Make makefile" ~label:"Make makefile" ~callback:External.rocq_makefile;
  ];

  menu debug_menu [
    item "Debug" ~label:"_Debug";
    item "Toggle breakpoint" ~label:"_Toggle breakpoint" ~accel:"F8" ~stock:`MEDIA_RECORD
      ~callback:MiscMenu.toggle_breakpoint;
    item "Continue" ~label:"_Continue" ~accel:"F9" ~stock:`MEDIA_NEXT ~callback:Nav.continue;
    item "Step in" ~label:"Step in" ~accel:"F10" ~stock:`MEDIA_PLAY ~callback:Nav.step_in;
    item "Step out" ~label:"Step out" ~accel:"<Shift>F10" ~stock:`MEDIA_FORWARD ~callback:Nav.step_out;
    (* todo: consider other names for Break and Interrupt to be clearer to users *)
    item "Break" ~label:"Break" ~accel:"F11" ~stock:`MEDIA_PAUSE ~callback:Nav.break;
    item "Show debug panel" ~label:"Show debug panel" ~callback:Nav.show_debugger;
  ];

  menu windows_menu [
    item "Windows" ~label:"_Windows";
    item "Detach Proof" ~label:"Detach _Proof" ~callback:MiscMenu.detach_view
  ];

  menu help_menu [
    item "Help" ~label:"_Help";
    item "Browse Coq Manual" ~label:"Browse Coq _Manual" ~accel:"<Shift>F1" ~stock:`HELP
      ~callback:(fun _ ->
        browse notebook#current_term.messages#default_route#add_string Coq_config.wwwrefman);
    item "Browse Coq Library" ~label:"Browse Coq _Library" ~accel:"<Primary><Shift>F1" ~stock:`HELP
      ~callback:(fun _ ->
        browse notebook#current_term.messages#default_route#add_string Coq_config.wwwstdlib);
    item "Help for keyword" ~label:"Help for _keyword" ~accel:"F1"
      ~callback:(fun _ -> on_current_term (fun sn ->
        browse_keyword sn.messages#default_route#add_string (get_current_word sn)));
    item "Help for μPG mode" ~label:"Help for μPG mode"
      ~callback:(fun _ -> on_current_term (fun sn ->
         sn.messages#default_route#clear;
         sn.messages#default_route#add_string (MicroPG.get_documentation ())));
    item "About Coq" ~label:"_About" ~stock:`ABOUT
      ~callback:MiscMenu.about
  ];

  Rocqide_ui.init ();
  Rocqide_ui.ui_m#insert_action_group file_menu 0;
  Rocqide_ui.ui_m#insert_action_group export_menu 0;
  Rocqide_ui.ui_m#insert_action_group edit_menu 0;
  Rocqide_ui.ui_m#insert_action_group view_menu 0;
  Rocqide_ui.ui_m#insert_action_group navigation_menu 0;
  Rocqide_ui.ui_m#insert_action_group templates_menu 0;
  Rocqide_ui.ui_m#insert_action_group tools_menu 0;
  Rocqide_ui.ui_m#insert_action_group queries_menu 0;
  Rocqide_ui.ui_m#insert_action_group compile_menu 0;
  Rocqide_ui.ui_m#insert_action_group debug_menu 0;
  Rocqide_ui.ui_m#insert_action_group windows_menu 0;
  Rocqide_ui.ui_m#insert_action_group help_menu 0;
  w#add_accel_group Rocqide_ui.ui_m#get_accel_group ;
  GtkMain.Rc.parse_string "gtk-can-change-accels = 1";
  if Config.gtk_platform <> `QUARTZ
  then vbox#pack (Rocqide_ui.ui_m#get_widget "/RocqIDE MenuBar");

  (* Connect some specific actions *)
  let unicode = Rocqide_ui.ui_m#get_action "ui/RocqIDE MenuBar/Tools/LaTeX-to-unicode" in
  let callback b = unicode#set_sensitive b in
  let () = callback unicode_binding#get in
  let _ = unicode_binding#connect#changed ~callback in

  (* Toolbar *)
  let tbar = GtkButton.Toolbar.cast
      ((Rocqide_ui.ui_m#get_widget "/RocqIDE ToolBar")#as_widget)
  in
  let () = GtkButton.Toolbar.set
    ~orientation:`HORIZONTAL ~style:`ICONS tbar
  in
  let toolbar = new GButton.toolbar tbar in
  let () = vbox#pack toolbar#coerce in

  (* Emacs/PG mode *)
  MicroPG.init w notebook all_menus;

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

  (* Location display *)
  let l = GMisc.label
    ~text:"Line:     1 Char:   1 Offset:     0"
    ~packing:lower_hbox#pack ()
  in
  let () = l#coerce#misc#set_name "location" in
  let () = set_location := l#set_text in

  (* Progress Bar *)
  let pbar = GRange.progress_bar ~pulse_step:0.1 () in
  let () = lower_hbox#pack pbar#coerce in
  let ready () = pbar#set_fraction 0.0 in
  let pulse sn =
    if RocqDriver.is_stopped_in_debugger sn.rocqtop then
      (pbar#set_pulse_step 0.0; pbar#pulse ())  (* stops slider at left end, not ideal *)
    else if RocqDriver.is_computing sn.rocqtop then
      (pbar#set_pulse_step 0.1; pbar#pulse ())
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
    let processed, to_process, jobs = sn.rocqops#get_slaves_status in
    let missing = to_process - processed in
    let n_err = sn.rocqops#get_n_errors in
    if n_err > 0 then
      slaveinfo#set_text (Printf.sprintf
        "%d / <span foreground=\"#FF0000\">%d</span>" missing n_err)
    else
      slaveinfo#set_text (Printf.sprintf "%d / %d" missing n_err);
    slaveinfo#set_use_markup true;
    sn.warnpage#update sn.rocqops#get_warnings;
    sn.errpage#update sn.rocqops#get_errors;
    sn.jobpage#update (Util.pi3 sn.rocqops#get_slaves_status) in
  let callback () = on_current_term update; true in
  let _ = Glib.Timeout.add ~ms:300 ~callback in

  (* Initializing hooks *)
  let refresh_style style =
    let style = style_manager#style_scheme style in
    let iter_session v =
      v.script#source_buffer#set_style_scheme style;
      v.proof#source_buffer#set_style_scheme style;
      v.messages#default_route#source_buffer#set_style_scheme style in
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

  (* Showtime ! *)
  w#show ();
  w


(** {2 Rocqide main function } *)

let make_file_buffer f =
  let f = if Filename.check_suffix f ".v" then f else f^".v" in
  FileAux.load_file ~maycreate:true f

let make_scratch_buffer () =
  let session = create_session None in
  let _ = notebook#append_term session in
  ()

let main files =
  let w = build_ui () in
  reset_reload_timer ();
  reset_autosave_timer ();
  (match files with
    | [] -> make_scratch_buffer ()
    | _ -> List.iter make_file_buffer files);
  notebook#goto_page 0;
  MiscMenu.initial_about ();
  on_current_term (fun t -> t.script#misc#grab_focus ());
  Minilib.log "End of Rocqide.main";
  w

(** {2 Argument parsing } *)

(** By default, the rocqtop we try to launch is exactly the current rocqide
    full name, with the last occurrence of "rocqide" replaced by "coqtop".
    This should correctly handle the ".opt", ".byte", ".exe" situations.
    If the replacement fails, we default to "coqtop", hoping it's somewhere
    in the path. Note that the -coqtop option to rocqide overrides
    this default coqtop path *)

let rocqide_specific_usage = Boot.Usage.{
  executable_name = "rocqide";
  extra_args = "";
  extra_options = "\n\
RocqIDE specific options:\
\n  -f _CoqProjectFile         set _CoqProject file to _CoqProjectFile\
\n  -unicode-bindings f1 .. f2 load files f1..f2 with extra unicode bindings\
\n  -coqtop dir                look for rocqidetop in dir\
\n  -coqtop-flags              extra flags for the rocqtop subprocess\
\n  -debug                     enable debug mode\
\n  -xml-debug                 enable debug mode and print XML messages to/from RocqIDE\
\n"
}

let read_rocqide_args argv =
  let set_debug () =
    CDebug.set_debug_all true;
(*    CDebug.(set_flag misc false)*)
    Minilib.debug := true;
  in
  let rec filter_rocqtop rocqtop project_files bindings_files out = function
    |"-unicode-bindings" :: sfilenames :: args ->
      let filenames = Str.split (Str.regexp ",") sfilenames in
      filter_rocqtop rocqtop project_files (filenames @ bindings_files) out args
    |"-coqtop" :: prog :: args ->
      if rocqtop = None then filter_rocqtop (Some prog) project_files bindings_files out args
      else (output_string stderr "Error: multiple -coqtop options"; exit 1)
    |"-coqtop" :: [] ->
      output_string stderr "Error: missing argument after -coqtop"; exit 1
    |"-f" :: file :: args ->
      if project_files <> None then
        (output_string stderr "Error: multiple -f options"; exit 1);
      let d = CUnix.canonical_path_name (Filename.dirname file) in
      let warning_fn x = Format.eprintf "%s@\n%!" x in
      let p = CoqProject_file.read_project_file ~warning_fn file in
      filter_rocqtop rocqtop (Some (d,p)) bindings_files out args
    |"-f" :: [] ->
      output_string stderr "Error: missing project file name"; exit 1
    |"-debug"::args ->
      set_debug ();
      filter_rocqtop rocqtop project_files bindings_files out args
    |"-xml-debug"::args ->
      set_debug ();
      Flags.xml_debug := true;
      filter_rocqtop rocqtop project_files bindings_files ("-xml-debug"::out) args
    |"-coqtop-flags" :: flags :: args->
      RocqDriver.ideslave_rocqtop_flags := Some flags;
      filter_rocqtop rocqtop project_files bindings_files out args
    | ("-v" | "--version") :: _ ->
      (* This does the same thing as Usage.version () but printed differently *)
      Printf.printf "RocqIDE, version %s\n" Coq_config.version;
      (* Unlike rocqtop we don't accumulate queries so we exit immediately *)
      exit 0
    | ("-h"|"-H"|"-?"|"-help"|"--help") :: _ ->
      Boot.Usage.print_usage stderr rocqide_specific_usage;
      exit 0
    | arg::args when out = [] && CString.is_prefix "-psn_" arg ->
      (* argument added by MacOS during .app launch *)
      filter_rocqtop rocqtop project_files bindings_files out args
    | arg::args -> filter_rocqtop rocqtop project_files bindings_files (arg::out) args
    |[] -> (rocqtop,project_files,bindings_files,List.rev out)
  in
  let rocqtop,project_files,bindings_files,argv = filter_rocqtop None None [] [] argv in
  Ideutils.custom_rocqtop := rocqtop;
  custom_project_file := project_files;
  Unicode_bindings.load_files bindings_files;
  argv


(** {2 Signal handling } *)

(** The Ctrl-C (sigint) is handled as a interactive quit.
    For most of the other catchable signals we launch
    an emergency save of opened files and then exit. *)

let signals_to_crash =
  [Sys.sigabrt; Sys.sigalrm; Sys.sigfpe; Sys.sighup;
   Sys.sigill; Sys.sigpipe; Sys.sigquit; Sys.sigusr2]

let set_signal_handlers ?parent () =
  try
    Sys.set_signal Sys.sigint (Sys.Signal_handle (File.quit ?parent));
    List.iter
      (fun i -> Sys.set_signal i (Sys.Signal_handle FileAux.crash_save))
      signals_to_crash
  with _ -> Minilib.log "Signal ignored (normal if Win32)"
