(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Preferences
open Gtk_parsing
open Ideutils

type flag = [ `COMMENT | `UNSAFE ]

type ide_info = {
  start : GText.mark;
  stop : GText.mark;
  flags : flag list;
}

class type _analyzed_view =
object

  method kill_detached_views : unit -> unit
  method add_detached_view : GWindow.window -> unit
  method remove_detached_view : GWindow.window -> unit

  method filename : string option
  method stats :  Unix.stats option
  method update_stats : unit
  method revert : unit
  method auto_save : unit
  method save : string -> bool
  method save_as : string -> bool
  method get_insert : GText.iter
  method get_start_of_input : GText.iter
  method go_to_insert : Coq.handle -> unit
  method go_to_next_occ_of_cur_word : unit
  method go_to_prev_occ_of_cur_word : unit
  method tactic_wizard : Coq.handle -> string list -> unit
  method insert_message : string -> unit
  method process_next_phrase : Coq.handle -> bool -> unit
  method process_until_end_or_error : Coq.handle -> unit
  method recenter_insert : unit
  method erroneous_reset_initial : Coq.handle -> unit
  method requested_reset_initial : Coq.handle -> unit
  method set_message : string -> unit
  method raw_coq_query : Coq.handle -> string -> unit
  method show_goals : Coq.handle -> unit
  method backtrack_last_phrase : Coq.handle -> unit
  method help_for_keyword : unit -> unit
end


type viewable_script = {
  script : Wg_ScriptView.script_view;
  tab_label : GMisc.label;
  proof_view : Wg_ProofView.proof_view;
  message_view : Wg_MessageView.message_view;
  analyzed_view : _analyzed_view;
  toplvl : Coq.coqtop;
  command : Wg_Command.command_window;
  finder : Wg_Find.finder;
}

let kill_session s =
  s.analyzed_view#kill_detached_views ();
  Coq.close_coqtop s.toplvl

let build_session s =
  let session_paned = GPack.paned `VERTICAL () in
  let session_box =
    GPack.vbox ~packing:(session_paned#pack1 ~shrink:false ~resize:true) ()
  in
  let eval_paned = GPack.paned `HORIZONTAL ~border_width:5
    ~packing:(session_box#pack ~expand:true) () in
  let script_frame = GBin.frame ~shadow_type:`IN
    ~packing:eval_paned#add1 () in
  let script_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:script_frame#add () in
  let state_paned = GPack.paned `VERTICAL
    ~packing:eval_paned#add2 () in
  let proof_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add1 () in
  let proof_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:proof_frame#add () in
  let message_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add2 () in
  let message_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:message_frame#add () in
  let session_tab = GPack.hbox ~homogeneous:false () in
  let img = GMisc.image ~icon_size:`SMALL_TOOLBAR
    ~packing:session_tab#pack () in
  let _ =
    s.script#buffer#connect#modified_changed
      ~callback:(fun () -> if s.script#buffer#modified
        then img#set_stock `SAVE
        else img#set_stock `YES) in
  let _ =
    eval_paned#misc#connect#size_allocate
      ~callback:
      (let old_paned_width = ref 2 in
       let old_paned_height = ref 2 in
       (fun {Gtk.width=paned_width;Gtk.height=paned_height} ->
	 if !old_paned_width <> paned_width || !old_paned_height <> paned_height then (
	   eval_paned#set_position (eval_paned#position * paned_width / !old_paned_width);
	   state_paned#set_position (state_paned#position * paned_height / !old_paned_height);
	   old_paned_width := paned_width;
	   old_paned_height := paned_height;
	 )))
  in
  session_box#pack s.finder#coerce;
  session_paned#pack2 ~shrink:false ~resize:false (s.command#frame#coerce);
  script_scroll#add s.script#coerce;
  proof_scroll#add s.proof_view#coerce;
  message_scroll#add s.message_view#coerce;
  session_tab#pack s.tab_label#coerce;
  img#set_stock `YES;
  eval_paned#set_position 1;
  state_paned#set_position 1;
  (Some session_tab#coerce,None,session_paned#coerce)

let session_notebook =
  Wg_Notebook.create build_session kill_session
    ~border_width:2 ~show_border:false ~scrollable:true ()

let cb = GData.clipboard Gdk.Atom.primary

let update_notebook_pos () =
  let pos =
    match current.vertical_tabs, current.opposite_tabs with
      | false, false -> `TOP
      | false, true  -> `BOTTOM
      | true , false -> `LEFT
      | true , true  -> `RIGHT
  in
  session_notebook#set_tab_pos pos

(** * Coqide's handling of signals *)

(** We ignore Ctrl-C, and for most of the other catchable signals
    we launch an emergency save of opened files and then exit *)

let signals_to_crash = [Sys.sigabrt; Sys.sigalrm; Sys.sigfpe; Sys.sighup;
			Sys.sigill; Sys.sigpipe; Sys.sigquit;
			(* Sys.sigsegv; Sys.sigterm;*) Sys.sigusr2]

let crash_save i =
  (*  ignore (Unix.sigprocmask Unix.SIG_BLOCK signals_to_crash);*)
  Minilib.log "Trying to save all buffers in .crashcoqide files";
  let count = ref 0 in
  List.iter
    (function {script=view; analyzed_view = av } ->
      (let filename = match av#filename with
	| None ->
	  incr count;
	  "Unnamed_coqscript_"^(string_of_int !count)^".crashcoqide"
	| Some f -> f^".crashcoqide"
       in
       try
	 if try_export filename (view#buffer#get_text ()) then
	   Minilib.log ("Saved "^filename)
	 else Minilib.log ("Could not save "^filename)
       with _ -> Minilib.log ("Could not save "^filename))
    )
    session_notebook#pages;
  Minilib.log "Done. Please report.";
  if i <> 127 then exit i

let ignore_break () =
  List.iter
    (fun i ->
      try Sys.set_signal i (Sys.Signal_handle crash_save)
      with _ -> Minilib.log "Signal ignored (normal if Win32)")
    signals_to_crash;
  Sys.set_signal Sys.sigint Sys.Signal_ignore


exception Unsuccessful

let force_reset_initial () =
  Minilib.log "Reset Initial";
  let term = session_notebook#current_term in
  Coq.reset_coqtop term.toplvl term.analyzed_view#requested_reset_initial

let break () =
  Minilib.log "User break received";
  Coq.break_coqtop session_notebook#current_term.toplvl

let do_if_not_computing term text f =
  let threaded_task () =
    let info () = Minilib.log ("Discarded query:" ^ text) in
    try Coq.try_grab term.toplvl f info
    with
    | e ->
      let msg = "Unknown error, please report:\n" ^ (Printexc.to_string e) in
      term.analyzed_view#set_message msg
  in
  Minilib.log ("Launching thread " ^ text);
  ignore (Thread.create threaded_task ())

let warning msg =
  GToolbox.message_box ~title:"Warning"
    ~icon:(let img = GMisc.image () in
	   img#set_stock `DIALOG_WARNING;
	   img#set_icon_size `DIALOG;
	   img#coerce)
    msg

let remove_current_view_page () =
  let do_remove () =
    let c = session_notebook#current_page in
    session_notebook#remove_page c
  in
  let current = session_notebook#current_term in
  if not current.script#buffer#modified then do_remove ()
  else
    match GToolbox.question_box ~title:"Close"
      ~buttons:["Save Buffer and Close";
                "Close without Saving";
                "Don't Close"]
      ~default:0
      ~icon:(let img = GMisc.image () in
             img#set_stock `DIALOG_WARNING;
             img#set_icon_size `DIALOG;
             img#coerce)
      "This buffer has unsaved modifications"
    with
      | 1 ->
        begin match current.analyzed_view#filename with
          | None ->
            begin match select_file_for_save ~title:"Save file" () with
              | None -> ()
              | Some f ->
                if current.analyzed_view#save_as f then begin
                  flash_info ("File " ^ f ^ " saved") ;
                  do_remove ()
                end else
                  warning  ("Save Failed (check if " ^ f ^ " is writable)")
            end
          | Some f ->
            if current.analyzed_view#save f then begin
              flash_info ("File " ^ f ^ " saved") ;
              do_remove ()
            end else
              warning  ("Save Failed (check if " ^ f ^ " is writable)")
        end
      | 2 -> do_remove ()
      | _ -> ()

module Opt = Coq.PrintOpt

let print_items = [
  ([Opt.implicit],"Display implicit arguments","Display _implicit arguments",
   "i",false);
  ([Opt.coercions],"Display coercions","Display _coercions","c",false);
  ([Opt.raw_matching],"Display raw matching expressions",
   "Display raw _matching expressions","m",true);
  ([Opt.notations],"Display notations","Display _notations","n",true);
  ([Opt.all_basic],"Display all basic low-level contents",
   "Display _all basic low-level contents","a",false);
  ([Opt.existential],"Display existential variable instances",
   "Display _existential variable instances","e",false);
  ([Opt.universes],"Display universe levels","Display _universe levels",
   "u",false);
  ([Opt.all_basic;Opt.existential;Opt.universes], "Display all low-level contents",
   "Display all _low-level contents","l",false)
]

let setopts ct opts v =
  let opts = List.map (fun o -> (o, v)) opts in
  Coq.PrintOpt.set ct opts

let get_current_word () =
  match session_notebook#current_term,cb#text with
    | {script=script; analyzed_view=av;},None ->
      Minilib.log "None selected";
      let it = av#get_insert in
      let start = find_word_start it in
      let stop = find_word_end start in
      script#buffer#move_mark `SEL_BOUND ~where:start;
      script#buffer#move_mark `INSERT ~where:stop;
      script#buffer#get_text ~slice:true ~start ~stop ()
    | _,Some t ->
      Minilib.log "Some selected";
      Minilib.log t;
      t

let input_channel b ic =
  let buf = String.create 1024 and len = ref 0 in
  while len := input ic buf 0 1024; !len > 0 do
    Buffer.add_substring b buf 0 !len
  done

let with_file handler name ~f =
  try
    let ic = open_in_gen [Open_rdonly;Open_creat] 0o644 name in
    try f ic; close_in ic with e -> close_in ic; raise e
  with Sys_error s -> handler s

(** Cut a part of the buffer in sentences and tag them.
    May raise [Coq_lex.Unterminated] when the zone ends with
    an unterminated sentence. *)

let split_slice_lax (buffer: GText.buffer) from upto =
  buffer#remove_tag ~start:from ~stop:upto Tags.Script.comment_sentence;
  buffer#remove_tag ~start:from ~stop:upto Tags.Script.sentence;
  let slice = buffer#get_text ~start:from ~stop:upto () in
  let rec split_substring str =
    let off_conv = byte_offset_to_char_offset str in
    let slice_len = String.length str in
    let is_comment,end_off = Coq_lex.delimit_sentence str
    in
    let start = from#forward_chars (off_conv end_off) in
    let stop = start#forward_char in
    buffer#apply_tag ~start ~stop
      (if is_comment then Tags.Script.comment_sentence else Tags.Script.sentence);
    let next = end_off + 1 in
    if next < slice_len then begin
      ignore (from#nocopy#forward_chars (off_conv next));
      split_substring (String.sub str next (slice_len - next))
    end
  in
  split_substring slice

(** Searching forward and backward a position fulfilling some condition *)

let rec forward_search cond (iter:GText.iter) =
  if iter#is_end || cond iter then iter
  else forward_search cond iter#forward_char

let rec backward_search cond (iter:GText.iter) =
  if iter#is_start || cond iter then iter
  else backward_search cond iter#backward_char

let is_sentence_end s = s#has_tag Tags.Script.sentence || s#has_tag Tags.Script.comment_sentence
let is_char s c = s#char = Char.code c

(** Search backward the first character of a sentence, starting at [iter]
    and going at most up to [soi] (meant to be the end of the locked zone).
    Raise [Not_found] when no proper sentence start has been found,
    in particular when the final "." of the locked zone is followed
    by a non-blank character outside the locked zone. This non-blank
    character will be signaled as erroneous in [tag_on_insert] below. *)

let grab_sentence_start (iter:GText.iter) soi =
  let cond iter =
    if iter#compare soi < 0 then raise Not_found;
    let prev = iter#backward_char in
    is_sentence_end prev &&
      (not (is_char prev '.') ||
       List.exists (is_char iter) [' ';'\n';'\r';'\t'])
  in
  backward_search cond iter

(** Search forward the first character immediately after a sentence end *)

let rec grab_sentence_stop (start:GText.iter) =
  (forward_search is_sentence_end start)#forward_char

(** Search forward the first character immediately after a "." sentence end
    (and not just a "{" or "}" or comment end *)

let rec grab_ending_dot (start:GText.iter) =
  let is_ending_dot s = is_sentence_end s && s#char = Char.code '.' in
  (forward_search is_ending_dot start)#forward_char

(** Retag a zone that has been edited *)

let tag_on_insert buffer =
  try
    (* the start of the non-locked zone *)
    let soi = buffer#get_iter_at_mark (`NAME "start_of_input") in
    (* the inserted zone is between [prev_insert] and [insert] *)
    let insert = buffer#get_iter_at_mark `INSERT in
    let prev_insert = buffer#get_iter_at_mark (`NAME "prev_insert") in
    (* [prev_insert] is normally always before [insert] even when deleting.
      Let's check this nonetheless *)
    let prev_insert =
      if insert#compare prev_insert < 0 then insert else prev_insert
    in
    let start = grab_sentence_start prev_insert soi in
    (** The status of "{" "}" as sentence delimiters is too fragile.
        We retag up to the next "." instead. *)
    let stop = grab_ending_dot insert in
    try split_slice_lax buffer start stop
    with Coq_lex.Unterminated ->
      try split_slice_lax buffer start buffer#end_iter
      with Coq_lex.Unterminated -> ()
  with Not_found ->
    (* This is raised by [grab_sentence_start] *)
    let err_pos = buffer#get_iter_at_mark (`NAME "start_of_input") in
    buffer#apply_tag Tags.Script.error ~start:err_pos ~stop:err_pos#forward_char

let force_retag buffer =
  try split_slice_lax buffer buffer#start_iter buffer#end_iter
  with Coq_lex.Unterminated -> ()

(* GtkSource view should handle that one day !!!
let toggle_proof_visibility (buffer:GText.buffer) (cursor:GText.iter) =
  (* move back twice if not into proof_decl,
   * once if into proof_decl and back_char into_proof_decl,
   * don't move if into proof_decl and back_char not into proof_decl *)
  if not (cursor#has_tag Tags.Script.proof_decl) then
    ignore (cursor#nocopy#backward_to_tag_toggle (Some Tags.Script.proof_decl));
  if cursor#backward_char#has_tag Tags.Script.proof_decl then
    ignore (cursor#nocopy#backward_to_tag_toggle (Some Tags.Script.proof_decl));
  let decl_start = cursor in
  let prf_end = decl_start#forward_to_tag_toggle (Some Tags.Script.qed) in
  let decl_end = grab_ending_dot decl_start in
  let prf_end = grab_ending_dot prf_end in
  let prf_end = prf_end#forward_char in
  if decl_start#has_tag Tags.Script.folded then (
    buffer#remove_tag ~start:decl_start ~stop:decl_end Tags.Script.folded;
    buffer#remove_tag ~start:decl_end ~stop:prf_end Tags.Script.hidden)
  else (
    buffer#apply_tag ~start:decl_start ~stop:decl_end Tags.Script.folded;
    buffer#apply_tag ~start:decl_end ~stop:prf_end Tags.Script.hidden)
*)

(** The arguments that will be passed to coqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
let custom_project_files = ref []
let sup_args = ref []

class analyzed_view (_script:Wg_ScriptView.script_view)
  (_pv:Wg_ProofView.proof_view) (_mv:Wg_MessageView.message_view) _ct _fn =
object(self)
  val input_view = _script
  val input_buffer = _script#source_buffer
  val proof_view = _pv
  val message_view = _mv
  val cmd_stack = Stack.create ()
  val mycoqtop = _ct

  val mutable filename = _fn
  val mutable stats = None
  val mutable last_modification_time = 0.
  val mutable last_auto_save_time = 0.
  val mutable detached_views = []

  val hidden_proofs = Hashtbl.create 32

  method add_detached_view (w:GWindow.window) =
    detached_views <- w::detached_views
  method remove_detached_view (w:GWindow.window) =
    detached_views <- List.filter (fun e -> w#misc#get_oid<>e#misc#get_oid) detached_views

  method kill_detached_views () =
    List.iter (fun w -> w#destroy ()) detached_views;
    detached_views <- []

  method filename = filename
  method stats = stats
  method update_stats =
    match filename with
      | Some f -> stats <- my_stat f
      | _ -> ()

  method revert =
    match filename with
      | Some f -> begin
        let do_revert () = begin
          push_info "Reverting buffer";
          try
            Coq.reset_coqtop mycoqtop self#requested_reset_initial;
            let b = Buffer.create 1024 in
            with_file flash_info f ~f:(input_channel b);
            let s = try_convert (Buffer.contents b) in
            input_buffer#set_text s;
            self#update_stats;
            input_buffer#place_cursor ~where:input_buffer#start_iter;
            input_buffer#set_modified false;
            pop_info ();
            flash_info "Buffer reverted";
            force_retag (input_buffer :> GText.buffer);
          with _  ->
            pop_info ();
            flash_info "Warning: could not revert buffer";
        end
        in
        if input_buffer#modified then
          match (GToolbox.question_box
                   ~title:"Modified buffer changed on disk"
                   ~buttons:["Revert from File";
                             "Overwrite File";
                             "Disable Auto Revert"]
                   ~default:0
                   ~icon:(stock_to_widget `DIALOG_WARNING)
                   "Some unsaved buffers changed on disk"
          )
          with 1 -> do_revert ()
            | 2 -> if self#save f then flash_info "Overwritten" else
                flash_info "Could not overwrite file"
            | _ ->
              Minilib.log "Auto revert set to false";
              current.global_auto_revert <- false;
              disconnect_revert_timer ()
        else do_revert ()
      end
      | None -> ()

  method save f =
    if try_export f (input_buffer#get_text ()) then begin
      filename <- Some f;
      input_buffer#set_modified false;
      stats <- my_stat f;
      (match self#auto_save_name with
        | None -> ()
        | Some fn -> try Sys.remove fn with _ -> ());
      true
    end
    else false

  method private auto_save_name =
    match filename with
      | None -> None
      | Some f ->
        let dir = Filename.dirname f in
        let base = (fst current.auto_save_name) ^
          (Filename.basename f) ^
          (snd current.auto_save_name)
        in Some (Filename.concat dir base)

  method private need_auto_save =
    input_buffer#modified &&
      last_modification_time > last_auto_save_time

  method auto_save =
    if self#need_auto_save then begin
      match self#auto_save_name with
        | None -> ()
        | Some fn ->
          try
            last_auto_save_time <- Unix.time();
            Minilib.log ("Autosave time: "^(string_of_float (Unix.time())));
            if try_export fn (input_buffer#get_text ()) then begin
              flash_info ~delay:1000 "Autosaved"
            end
            else warning
              ("Autosave failed (check if " ^ fn ^ " is writable)")
          with _ ->
            warning ("Autosave: unexpected error while writing "^fn)
    end

  method save_as f =
    if Sys.file_exists f then
      match (GToolbox.question_box ~title:"File exists on disk"
               ~buttons:["Overwrite";
                         "Cancel";]
               ~default:1
               ~icon:
               (let img = GMisc.image () in
                img#set_stock `DIALOG_WARNING;
                img#set_icon_size `DIALOG;
                img#coerce)
               ("File "^f^" already exists")
      )
      with 1 -> self#save f
        | _ -> false
    else self#save f

  method insert_message s =
    message_view#push Interface.Notice s

  method set_message s =
    message_view#clear ();
    message_view#push Interface.Notice s

  method private push_message level content =
    message_view#push level content

  method get_start_of_input =  input_buffer#get_iter_at_mark (`NAME "start_of_input")

  method get_insert = get_insert input_buffer

  method recenter_insert =
    (* BUG : to investigate further:
       FIXED : Never call  GMain.* in thread !
       PLUS : GTK BUG ??? Cannot be called from a thread...
       ADDITION: using sync instead of async causes deadlock...*)
    ignore (GtkThread.async (
      input_view#scroll_to_mark
        ~use_align:false
        ~yalign:0.75
        ~within_margin:0.25)
              `INSERT)

  method go_to_next_occ_of_cur_word =
    let cv = session_notebook#current_term in
    let av = cv.analyzed_view in
    let b = (cv.script)#buffer in
    let start = find_word_start (av#get_insert) in
    let stop = find_word_end start in
    let text = b#get_text ~start ~stop () in
    match stop#forward_search text with
      | None -> ()
      | Some(start, _) ->
        (b#place_cursor start;
         self#recenter_insert)

  method go_to_prev_occ_of_cur_word =
    let cv = session_notebook#current_term in
    let av = cv.analyzed_view in
    let b = (cv.script)#buffer in
    let start = find_word_start (av#get_insert) in
    let stop = find_word_end start in
    let text = b#get_text ~start ~stop () in
    match start#backward_search text with
      | None -> ()
      | Some(start, _) ->
        (b#place_cursor start;
         self#recenter_insert)

  method show_goals handle =
    Coq.PrintOpt.set_printing_width proof_view#width;
    match Coq.goals handle with
    | Interface.Fail (l, str) ->
      self#set_message ("Error in coqtop:\n"^str)
    | Interface.Good goals | Interface.Unsafe goals ->
      begin match Coq.evars handle with
      | Interface.Fail (l, str)->
        self#set_message ("Error in coqtop:\n"^str)
      | Interface.Good evs  | Interface.Unsafe evs ->
        proof_view#set_goals goals;
        proof_view#set_evars evs;
        proof_view#refresh ()
      end

  (* This method is intended to perform stateless commands *)
  method raw_coq_query handle phrase =
    let () = Minilib.log "raw_coq_query starting now" in
    let display_error s =
      if not (Glib.Utf8.validate s) then
        flash_info "This error is so nasty that I can't even display it."
      else self#insert_message s;
    in
    match Coq.interp handle self#push_message ~raw:true ~verbose:false phrase with
    | Interface.Fail (_, err) -> sync display_error err
    | Interface.Good msg | Interface.Unsafe msg -> sync self#insert_message msg

  method private find_phrase_starting_at (start:GText.iter) =
    try
      let start = grab_sentence_start start self#get_start_of_input in
      let stop = grab_sentence_stop start in
      (* Is this phrase non-empty and complete ? *)
      if stop#compare start > 0 && is_sentence_end stop#backward_char
      then Some (start,stop)
      else None
    with Not_found -> None

  (** [fill_command_queue until q] fills a command queue until the [until]
      condition returns true; it is fed with the number of phrases read and the
      iters enclosing the current sentence. *)
  method private fill_command_queue until queue =
    let rec loop len iter =
      let opt_sentence = self#find_phrase_starting_at iter in
      match opt_sentence with
      | None -> raise Exit
      | Some (start, stop) ->
        if until len start stop then raise Exit;
        input_buffer#apply_tag Tags.Script.to_process ~start ~stop;
        (* Check if this is a comment *)
        let is_comment = stop#backward_char#has_tag Tags.Script.comment_sentence in
        let flags = if is_comment then [`COMMENT] else [] in
        let payload = {
          start = `MARK (input_buffer#create_mark start);
          stop = `MARK (input_buffer#create_mark stop);
          flags = flags;
        } in
        Queue.push payload queue;
        if not stop#is_end then loop (succ len) stop
    in
    try loop 0 self#get_start_of_input with Exit -> ()

  method private process_command_queue ?(verbose = false) queue handle =
    let error = ref None in
    let info = ref [] in
    let current_flags = ref [] in
    let push_info level message = info := (level, message) :: !info in
    (* First, process until error *)
    Minilib.log "Begin command processing";
    while not (Queue.is_empty queue) && !error = None do
      let sentence = Queue.peek queue in
      (* If the line is not a comment, we interpret it. *)
      if not (List.mem `COMMENT sentence.flags) then begin
        let start = input_buffer#get_iter_at_mark sentence.start in
        let stop = input_buffer#get_iter_at_mark sentence.stop in
        let phrase = start#get_slice ~stop in
        match Coq.interp handle push_info ~verbose phrase with
        | Interface.Fail (loc, msg) ->
          error := Some (phrase, loc, msg);
        | Interface.Good msg ->
          push_info Interface.Notice msg;
          current_flags := []
        | Interface.Unsafe msg ->
          current_flags := [`UNSAFE]
      end;
      (* If there is no error, then we mark it done *)
      if !error = None then begin
        (* We reget the iters here because Gtk is unable to warranty that they
           were not modified meanwhile. Not really necessary but who knows... *)
        let start = input_buffer#get_iter_at_mark sentence.start in
        let stop = input_buffer#get_iter_at_mark sentence.stop in
        let sentence = { sentence with
          flags = !current_flags @ sentence.flags
        } in
        let tag =
          if List.mem `UNSAFE !current_flags then Tags.Script.unjustified
          else Tags.Script.processed
        in
        input_buffer#move_mark ~where:stop (`NAME "start_of_input");
        input_buffer#apply_tag tag ~start ~stop;
        input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
        (* Discard the old stack info and put it were it belongs *)
        ignore (Queue.pop queue);
        Stack.push sentence cmd_stack;
      end;
    done;
    (* Then clear all irrelevant commands *)
    while not (Queue.is_empty queue) do
      let sentence = Queue.pop queue in
      let start = input_buffer#get_iter_at_mark sentence.start in
      let stop = input_buffer#get_iter_at_mark sentence.stop in
      input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
      input_buffer#delete_mark sentence.start;
      input_buffer#delete_mark sentence.stop;
    done;
    (* Return the list of info messages and the error *)
    (List.rev !info, !error)

  method private show_error phrase loc msg = match loc with
  | None ->
    message_view#clear ();
    message_view#push Interface.Error msg
  | Some (start, stop) ->
    let soi = self#get_start_of_input in
    let start = soi#forward_chars (byte_offset_to_char_offset phrase start) in
    let stop = soi#forward_chars (byte_offset_to_char_offset phrase stop) in
    input_buffer#apply_tag Tags.Script.error ~start ~stop;
    input_buffer#place_cursor ~where:start;
    message_view#clear ();
    message_view#push Interface.Error msg

  (** Compute the phrases until [until] returns [true]. *)
  method private process_until until finish handle verbose =
    let queue = Queue.create () in
    (* Lock everything and fill the waiting queue *)
    push_info "Coq is computing";
    message_view#clear ();
    input_view#set_editable false;
    self#fill_command_queue until queue;
    (* Now unlock and process asynchronously *)
    input_view#set_editable true;
    let (msg, error) = self#process_command_queue ~verbose queue handle in
    pop_info ();
    (* Display the goal and any error *)
    self#show_goals handle;
    match error with
    | None ->
      if verbose then
        List.iter (fun (lvl, msg) -> self#push_message lvl msg) msg;
      finish ();
      self#recenter_insert
    | Some (phrase, loc, msg) ->
      self#show_error phrase loc msg

  method process_next_phrase handle verbose =
    let until len start stop = 1 <= len in
    let finish () = input_buffer#place_cursor self#get_start_of_input in
    self#process_until until finish handle verbose

  method private process_until_iter handle iter =
    let until len start stop =
      if current.stop_before then stop#compare iter > 0
      else start#compare iter >= 0
    in
    let finish () = () in
    self#process_until until finish handle false

  method process_until_end_or_error handle =
    self#process_until_iter handle input_buffer#end_iter

  (** Clear the command stack until [until] returns [true]. Returns the number
      of commands sent to Coqtop to backtrack. *)
  method private clear_command_stack until =
    let rec loop len real_len =
      if Stack.is_empty cmd_stack then real_len
      else
        let phrase = Stack.top cmd_stack in
        let is_comment = List.mem `COMMENT phrase.flags in
        let start = input_buffer#get_iter_at_mark phrase.start in
        let stop = input_buffer#get_iter_at_mark phrase.stop in
        if not (until len real_len start stop) then begin
          (* [until] has not been reached, so we clear this command *)
          ignore (Stack.pop cmd_stack);
          input_buffer#remove_tag Tags.Script.processed ~start ~stop;
          input_buffer#remove_tag Tags.Script.unjustified ~start ~stop;
          input_buffer#move_mark ~where:start (`NAME "start_of_input");
          input_buffer#delete_mark phrase.start;
          input_buffer#delete_mark phrase.stop;
          loop (succ len) (if is_comment then real_len else succ real_len)
        end else
          real_len
    in
    loop 0 0

  (** Actually performs the undoing *)
  method private undo_command_stack handle n =
    match Coq.rewind handle n with
    | Interface.Good n | Interface.Unsafe n ->
      let until _ len _ _ = n <= len in
      (* Coqtop requested [n] more ACTUAL backtrack *)
      ignore (self#clear_command_stack until)
    | Interface.Fail (l, str) ->
      self#set_message
        ("Error while backtracking: " ^ str ^
          "\nCoqIDE and coqtop may be out of sync, you may want to use Restart.")

  (** Wrapper around the raw undo command *)
  method private backtrack_until until finish handle =
    push_info "Coq is undoing";
    message_view#clear ();
    (* Lock everything *)
    input_view#set_editable false;
    let to_undo = self#clear_command_stack until in
    self#undo_command_stack handle to_undo;
    input_view#set_editable true;
    pop_info ();
    finish ()

  method private backtrack_to_iter handle iter =
    let until _ _ _ stop = iter#compare stop >= 0 in
    let finish () = () in
    self#backtrack_until until finish handle;
    (* We may have backtracked too much: let's replay *)
    self#process_until_iter handle iter

  method backtrack_last_phrase handle =
    let until len _ _ _ = 1 <= len in
    let finish () = input_buffer#place_cursor self#get_start_of_input in
    self#backtrack_until until finish handle;
    self#show_goals handle

  method go_to_insert handle =
    let point = self#get_insert in
    if point#compare self#get_start_of_input >= 0
    then self#process_until_iter handle point
    else self#backtrack_to_iter handle point

  method private send_to_coq handle phrase =
    let display_error (loc, s) =
        if not (Glib.Utf8.validate s) then
          flash_info "This error is so nasty that I can't even display it."
        else self#insert_message s
      in
      Minilib.log "Send_to_coq starting now";
      match Coq.interp handle default_logger ~verbose:false phrase with
      | Interface.Fail (l, str) -> sync display_error (l, str); None
      | Interface.Good msg -> sync self#insert_message msg; Some []
      | Interface.Unsafe msg -> sync self#insert_message msg; Some [`UNSAFE]

  method private insert_this_phrase_on_success handle coqphrase insertphrase =
    let mark_processed flags =
      let stop = self#get_start_of_input in
      if stop#starts_line then
        input_buffer#insert ~iter:stop insertphrase
      else input_buffer#insert ~iter:stop ("\n"^insertphrase);
      let start = self#get_start_of_input in
      input_buffer#move_mark ~where:stop (`NAME "start_of_input");
      let tag =
        if List.mem `UNSAFE flags then Tags.Script.unjustified
        else Tags.Script.processed
      in
      input_buffer#apply_tag tag ~start ~stop;
      if self#get_insert#compare stop <= 0 then
        input_buffer#place_cursor ~where:stop;
      let ide_payload = {
        start = `MARK (input_buffer#create_mark start);
        stop = `MARK (input_buffer#create_mark stop);
        flags = [];
      } in
      Stack.push ide_payload cmd_stack;
      self#show_goals handle;
    in
    match self#send_to_coq handle coqphrase with
    | Some flags -> sync mark_processed flags; true
    | None ->
      sync (fun _ -> self#insert_message ("Unsuccessfully tried: "^coqphrase)) ();
      false

  method private generic_reset_initial handle =
    let start = input_buffer#start_iter in
    (* clear the stack *)
    while not (Stack.is_empty cmd_stack) do
      let phrase = Stack.pop cmd_stack in
      input_buffer#delete_mark phrase.start;
      input_buffer#delete_mark phrase.stop
    done;
    (* reset the buffer *)
    input_buffer#move_mark ~where:start (`NAME "start_of_input");
    input_buffer#remove_tag Tags.Script.processed start input_buffer#end_iter;
    input_buffer#remove_tag Tags.Script.unjustified start input_buffer#end_iter;
    input_buffer#remove_tag Tags.Script.to_process start input_buffer#end_iter;
    tag_on_insert (input_buffer :> GText.buffer);
    (* clear the views *)
    message_view#clear ();
    proof_view#clear ();
    (* apply the initial commands to coq *)
    self#include_file_dir_in_path handle;

  method erroneous_reset_initial handle =
    self#generic_reset_initial handle;
    (* warn the user *)
    warning "Coqtop died badly. Resetting."

  method requested_reset_initial handle =
    self#generic_reset_initial handle

  method tactic_wizard handle l =
    async message_view#clear ();
    ignore
      (List.exists
         (fun p ->
           self#insert_this_phrase_on_success handle
             ("progress "^p^".\n") (p^".\n")) l)

  method private include_file_dir_in_path handle =
    match filename with
      | None -> ()
      | Some f ->
	let dir = Filename.dirname f in
	match Coq.inloadpath handle dir with
	  | Interface.Fail (_,str) ->
	    self#set_message
	      ("Could not determine lodpath, this might lead to problems:\n"^str)
	  | Interface.Good true | Interface.Unsafe true -> ()
	  | Interface.Good false | Interface.Unsafe false ->
	    let cmd = Printf.sprintf "Add LoadPath \"%s\". "  dir in
	    match Coq.interp handle default_logger cmd with
	      | Interface.Fail (l,str) ->
		self#set_message ("Couln't add loadpath:\n"^str)
	      | Interface.Good _ | Interface.Unsafe _ -> ()

  method help_for_keyword () =
    browse_keyword (self#insert_message) (get_current_word ())

(** NB: Events during text edition:

    - [begin_user_action]
    - [insert_text] (or [delete_range] when deleting)
    - [changed]
    - [end_user_action]

   When pasting a text containing tags (e.g. the sentence terminators),
   there is actually many [insert_text] and [changed]. For instance,
   for "a. b.":

    - [begin_user_action]
    - [insert_text] (for "a")
    - [changed]
    - [insert_text] (for ".")
    - [changed]
    - [apply_tag] (for the tag of ".")
    - [insert_text] (for " b")
    - [changed]
    - [insert_text] (for ".")
    - [changed]
    - [apply_tag] (for the tag of ".")
    - [end_user_action]

  Since these copy-pasted tags may interact badly with the retag mechanism,
  we now don't monitor the "changed" event, but rather the "begin_user_action"
  and "end_user_action". We begin by setting a mark at the initial cursor
  point. At the end, the zone between the mark and the cursor is to be
  untagged and then retagged. *)

  initializer
    ignore (input_buffer#connect#insert_text
              ~callback:(fun it s ->
                if (it#compare self#get_start_of_input)<0
                then GtkSignal.stop_emit ();
                if String.length s > 1 then
                  (Minilib.log "insert_text: Placing cursor";input_buffer#place_cursor ~where:it)));
    ignore (input_buffer#connect#after#apply_tag
              ~callback:(fun tag ~start ~stop ->
                if (start#compare self#get_start_of_input)>=0
                then
                  begin
                    input_buffer#remove_tag
                      Tags.Script.processed
                      ~start
                      ~stop;
                    input_buffer#remove_tag
                      Tags.Script.unjustified
                      ~start
                      ~stop
                  end
              )
    );
    ignore (input_buffer#connect#begin_user_action
	      ~callback:(fun () ->
		           let here = input_buffer#get_iter_at_mark `INSERT in
			   input_buffer#move_mark (`NAME "prev_insert") here
	      )
    );
    ignore (input_buffer#connect#end_user_action
              ~callback:(fun () ->
                last_modification_time <- Unix.time ();
                let r = input_view#visible_rect in
                let stop =
                  input_view#get_iter_at_location
                    ~x:(Gdk.Rectangle.x r + Gdk.Rectangle.width r)
                    ~y:(Gdk.Rectangle.y r + Gdk.Rectangle.height r)
                in
                input_buffer#remove_tag
                  Tags.Script.error
                  ~start:self#get_start_of_input
                  ~stop;
                tag_on_insert (input_buffer :> GText.buffer)
              )
    );
    ignore (input_buffer#add_selection_clipboard cb);
    ignore (input_buffer#connect#after#mark_set
              ~callback:(fun it (m:Gtk.text_mark) ->
                !set_location
                  (Printf.sprintf
                     "Line: %5d Char: %3d" (self#get_insert#line + 1)
                     (self#get_insert#line_offset + 1));
                match GtkText.Mark.get_name m  with
                  | Some "insert" -> ()
                  | Some s ->
                    Minilib.log (s^" moved")
                  | None -> () )
    );
    ignore (input_buffer#connect#insert_text
              ~callback:(fun it s ->
                Minilib.log "Should recenter ?";
                if String.contains s '\n' then begin
                  Minilib.log "Should recenter: yes";
                  self#recenter_insert
                end));
    let callback () =
      if Coq.is_computing mycoqtop then pbar#pulse ();
      not (Coq.is_closed mycoqtop);
    in
    ignore (Glib.Timeout.add ~ms:300 ~callback);
    Coq.grab mycoqtop self#include_file_dir_in_path;
end

let last_make = ref "";;
let last_make_index = ref 0;;
let search_compile_error_regexp =
  Str.regexp
    "File \"\\([^\"]+\\)\", line \\([0-9]+\\), characters \\([0-9]+\\)-\\([0-9]+\\)";;

let search_next_error () =
  let _ = Str.search_forward search_compile_error_regexp !last_make !last_make_index in
  let f = Str.matched_group 1 !last_make
  and l = int_of_string (Str.matched_group 2 !last_make)
  and b = int_of_string (Str.matched_group 3 !last_make)
  and e = int_of_string (Str.matched_group 4 !last_make)
  and msg_index = Str.match_beginning ()
  in
  last_make_index := Str.group_end 4;
  (f,l,b,e,
   String.sub !last_make msg_index (String.length !last_make - msg_index))



(**********************************************************************)
(* session creation and primitive handling                            *)
(**********************************************************************)

let create_session file =
  let script_buffer =
    GSourceView2.source_buffer
      ~tag_table:Tags.Script.table
      ~highlight_matching_brackets:true
      ?language:(lang_manager#language current.source_language)
      ?style_scheme:(style_manager#style_scheme current.source_style)
      ()
  in
  let proof = Wg_ProofView.proof_view () in
  let message = Wg_MessageView.message_view () in
  let basename = GMisc.label ~text:(match file with
				      |None -> "*scratch*"
				      |Some f -> (Glib.Convert.filename_to_utf8 (Filename.basename f))
				   ) () in
  let coqtop_args = match file with
    |None -> !sup_args
    |Some the_file -> match current.read_project with
	|Ignore_args -> !sup_args
	|Append_args -> (Project_file.args_from_project the_file !custom_project_files current.project_file_name)
	   @(!sup_args)
	|Subst_args -> Project_file.args_from_project the_file !custom_project_files current.project_file_name
  in
  let reset = ref (fun _ -> ()) in
  let trigger handle = !reset handle in
  let ct = Coq.spawn_coqtop trigger coqtop_args in
  let script =
    Wg_ScriptView.script_view ct
      ~source_buffer:script_buffer
      ~show_line_numbers:true
      ~wrap_mode:`NONE () in
  let command = new Wg_Command.command_window ct in
  let finder = new Wg_Find.finder (script :> GText.view) in
  let legacy_av = new analyzed_view script proof message ct file in
  let () = reset := legacy_av#erroneous_reset_initial in
  let () = legacy_av#update_stats in
  let _ =
    script#buffer#create_mark ~name:"start_of_input" script#buffer#start_iter in
  let _ =
    script#buffer#create_mark ~name:"prev_insert" script#buffer#start_iter in
  let _ =
    GtkBase.Widget.add_events proof#as_widget [`ENTER_NOTIFY;`POINTER_MOTION] in
  let () =
    let fold accu (opts, _, _, _, dflt) =
      List.fold_left (fun accu opt -> (opt, dflt) :: accu) accu opts
    in
    let options = List.fold_left fold [] print_items in
    Coq.grab ct (fun handle -> Coq.PrintOpt.set handle options) in
  script#misc#set_name "ScriptWindow";
  script#buffer#place_cursor ~where:script#buffer#start_iter;
  proof#misc#set_can_focus true;
  message#misc#set_can_focus true;

  { tab_label=basename;
    script=script;
    proof_view=proof;
    message_view=message;
    analyzed_view=legacy_av;
    toplvl=ct;
    command=command;
    finder=finder;
  }

(* XXX - to be used later
   let load_session session filename encs =
   session.encoding <- List.find (IdeIO.load filename session.script#buffer) encs;
   session.tab_label#set_text (Glib.Convert.filename_to_utf8 (Filename.basename filename));
   session.filename <- filename;
   session.script#buffer#set_modified false


   let save_session session filename encs =
   session.encoding <- List.find (IdeIO.save session.script#buffer filename) encs;
   session.tab_label#set_text (Glib.Convert.filename_to_utf8 (Filename.basename filename));
   session.filename <- filename;
   session.script#buffer#set_modified false


   let init_session session =
   session.script#buffer#set_modified false;
   session.script#clear_undo;
   session.script#buffer#place_cursor session.script#buffer#start_iter
*)




(*********************************************************************)
(* functions called by the user interface                            *)
(*********************************************************************)
(* XXX - to be used later
   let do_open session filename =
   try
   load_session session filename ["UTF-8";"ISO-8859-1";"ISO-8859-15"];
   init_session session;
   ignore (session_notebook#append_term session)
   with _ -> ()


   let do_save session =
   try
   if session.script#buffer#modified then
   save_session session session.filename [session.encoding]
   with _ -> ()


   let choose_open =
   let last_filename = ref "" in fun session ->
   let open_dialog = GWindow.file_chooser_dialog ~action:`OPEN ~title:"Open file" ~modal:true () in
   let enc_frame = GBin.frame ~label:"File encoding" ~packing:(open_dialog#vbox#pack ~fill:false) () in
   let enc_entry = GEdit.entry ~text:(String.concat " " ["UTF-8";"ISO-8859-1";"ISO-8859-15"]) ~packing:enc_frame#add () in
   let error_dialog = GWindow.message_dialog ~message_type:`ERROR ~modal:true ~buttons:GWindow.Buttons.ok
   ~message:"Invalid encoding, please indicate the encoding to use." () in
   let open_response = function
   | `OPEN -> begin
   match open_dialog#filename with
   | Some fn -> begin
   try
   load_session session fn (Util.split_string_at ' ' enc_entry#text);
   session.analyzed_view <- Some (new analyzed_view session);
   init_session session;
   session_notebook#goto_page (session_notebook#append_term session);
   last_filename := fn
   with
   | Not_found -> open_dialog#misc#hide (); error_dialog#show ()
   | _ ->
   error_dialog#set_markup "Unknown error while loading file, aborting.";
   open_dialog#destroy (); error_dialog#destroy ()
   end
   | None -> ()
   end
   | `DELETE_EVENT -> open_dialog#destroy (); error_dialog#destroy ()
   in
   let _ = open_dialog#connect#response open_response in
   let _ = error_dialog#connect#response (fun x -> error_dialog#misc#hide (); open_dialog#show ()) in
   let filter_any = GFile.filter ~name:"Any" ~patterns:["*"] () in
   let filter_coq = GFile.filter ~name:"Coq source" ~patterns:["*.v"] () in
   open_dialog#add_select_button_stock `OPEN `OPEN;
   open_dialog#add_button_stock `CANCEL `DELETE_EVENT;
   open_dialog#add_filter filter_any;
   open_dialog#add_filter filter_coq;
   ignore(open_dialog#set_filename !last_filename);
   open_dialog#show ()


   let choose_save session =
   let save_dialog = GWindow.file_chooser_dialog ~action:`SAVE ~title:"Save file" ~modal:true () in
   let enc_frame = GBin.frame ~label:"File encoding" ~packing:(save_dialog#vbox#pack ~fill:false) () in
   let enc_entry = GEdit.entry ~text:(String.concat " " [session.encoding;"UTF-8";"ISO-8859-1";"ISO-8859-15"]) ~packing:enc_frame#add () in
   let error_dialog = GWindow.message_dialog ~message_type:`ERROR ~modal:true ~buttons:GWindow.Buttons.ok
   ~message:"Invalid encoding, please indicate the encoding to use." () in
   let save_response = function
   | `SAVE -> begin
   match save_dialog#filename with
   | Some fn -> begin
   try
   save_session session fn (Util.split_string_at ' ' enc_entry#text)
   with
   | Not_found -> save_dialog#misc#hide (); error_dialog#show ()
   | _ ->
   error_dialog#set_markup "Unknown error while saving file, aborting.";
   save_dialog#destroy (); error_dialog#destroy ()
   end
   | None -> ()
   end
   | `DELETE_EVENT -> save_dialog#destroy (); error_dialog#destroy ()
   in
   let _ = save_dialog#connect#response save_response in
   let _ = error_dialog#connect#response (fun x -> error_dialog#misc#hide (); save_dialog#show ()) in
   let filter_any = GFile.filter ~name:"Any" ~patterns:["*"] () in
   let filter_coq = GFile.filter ~name:"Coq source" ~patterns:["*.v"] () in
   save_dialog#add_select_button_stock `SAVE `SAVE;
   save_dialog#add_button_stock `CANCEL `DELETE_EVENT;
   save_dialog#add_filter filter_any;
   save_dialog#add_filter filter_coq;
   ignore(save_dialog#set_filename session.filename);
   save_dialog#show ()
*)

(* Nota: using && here has the advantage of working both under win32 and unix.
   If someday we want the main command to be tried even if the "cd" has failed,
   then we should use " ; " under unix but " & " under win32 (cf. #2363).
*)

let local_cd file =
  "cd " ^ Filename.quote (Filename.dirname file) ^ " && "

let do_print session =
  let av = session.analyzed_view in
  match av#filename with
    |None ->  flash_info "Cannot print: this buffer has no name"
    |Some f_name ->  begin
      let cmd =
        local_cd f_name ^
          current.cmd_coqdoc ^ " -ps " ^ Filename.quote (Filename.basename f_name) ^
          " | " ^ current.cmd_print
      in
      let print_window = GWindow.window ~title:"Print" ~modal:true ~position:`CENTER ~wm_class:"CoqIDE" ~wm_name: "CoqIDE"  () in
      let vbox_print = GPack.vbox ~spacing:10 ~border_width:10 ~packing:print_window#add () in
      let _ = GMisc.label ~justify:`LEFT ~text:"Print using the following command:" ~packing:vbox_print#add () in
      let print_entry = GEdit.entry ~text:cmd ~editable:true ~width_chars:80 ~packing:vbox_print#add () in
      let hbox_print = GPack.hbox ~spacing:10 ~packing:vbox_print#add () in
      let print_cancel_button = GButton.button ~stock:`CANCEL ~label:"Cancel" ~packing:hbox_print#add () in
      let print_button  = GButton.button ~stock:`PRINT  ~label:"Print"  ~packing:hbox_print#add () in
      let callback_print () =
        let cmd = print_entry#text in
        let s,_ = CUnix.run_command Ideutils.try_convert av#insert_message cmd in
        flash_info (cmd ^ if s = Unix.WEXITED 0 then " succeeded" else " failed");
        print_window#destroy ()
      in
      ignore (print_cancel_button#connect#clicked ~callback:print_window#destroy) ;
      ignore (print_button#connect#clicked ~callback:callback_print);
      print_window#misc#show ()
    end

let load_file handler f =
  let f = CUnix.correct_path f (Sys.getcwd ()) in
  try
    Minilib.log "Loading file starts";
    let is_f = CUnix.same_file f in
      if not (Util.list_fold_left_i
		(fun i found x -> if found then found else
                   let {analyzed_view=av} = x in
                     (match av#filename with
			| None -> false
			| Some fn ->
			    if is_f fn
			    then (session_notebook#goto_page i; true)
			    else false))
              0 false session_notebook#pages)
      then begin
	Minilib.log "Loading: must open";
	let b = Buffer.create 1024 in
	Minilib.log "Loading: get raw content";
	with_file handler f ~f:(input_channel b);
	Minilib.log "Loading: convert content";
	let s = do_convert (Buffer.contents b) in
	Minilib.log "Loading: create view";
	let session = create_session (Some f) in
	Minilib.log "Loading: adding view";
	let index = session_notebook#append_term session in
	let av = session.analyzed_view in
	Minilib.log "Loading: stats";
	av#update_stats;
	let input_buffer = session.script#buffer in
	Minilib.log "Loading: fill buffer";
	input_buffer#set_text s;
	input_buffer#place_cursor ~where:input_buffer#start_iter;
	force_retag input_buffer;
	Minilib.log ("Loading: switch to view "^ string_of_int index);
	session_notebook#goto_page index;
	Minilib.log "Loading: highlight";
	input_buffer#set_modified false;
	Minilib.log "Loading: clear undo";
	session.script#clear_undo ();
	Minilib.log "Loading: success";
        !refresh_editor_hook ();
      end
  with
    | e -> handler ("Load failed: "^(Printexc.to_string e))

let do_load file = load_file flash_info file

let saveall_f () =
  List.iter
    (function
       | {script = view ; analyzed_view = av} ->
           begin match av#filename with
             | None -> ()
             | Some f ->
		 ignore (av#save f)
           end
    )  session_notebook#pages

let forbid_quit_to_save () =
    begin try save_pref() with e -> flash_info "Cannot save preferences" end;
    (if List.exists
      (function
        | {script=view} -> view#buffer#modified
      )
      session_notebook#pages then
      match (GToolbox.question_box ~title:"Quit"
               ~buttons:["Save Named Buffers and Quit";
                         "Quit without Saving";
                         "Don't Quit"]
               ~default:0
               ~icon:
               (let img = GMisc.image () in
                img#set_stock `DIALOG_WARNING;
                img#set_icon_size `DIALOG;
                img#coerce)
               "There are unsaved buffers"
      )
      with 1 -> saveall_f () ; false
        | 2 -> false
        | _ -> true
    else false)||
      (let wait_window =
        GWindow.window ~modal:true ~wm_class:"CoqIde" ~wm_name:"CoqIde" ~kind:`POPUP
          ~title:"Terminating coqtops" () in
      let _ =
        GMisc.label ~text:"Terminating coqtops processes, please wait ..."
          ~packing:wait_window#add () in
      let warning_window =
        GWindow.message_dialog ~message_type:`WARNING ~buttons:GWindow.Buttons.yes_no
          ~message:
	  ("Some coqtops processes are still running.\n" ^
	     "If you quit CoqIDE right now, you may have to kill them manually.\n" ^
	     "Do you want to wait for those processes to terminate ?") () in
      let () = List.iter (fun _ -> session_notebook#remove_page 0) session_notebook#pages in
      let nb_try=ref (0) in
      let () = wait_window#show () in
      let () = while (Coq.coqtop_zombies () <> 0)&&(!nb_try <= 50) do
	incr nb_try;
	Thread.delay 0.1 ;
      done in
	if (!nb_try = 50) then begin
	  wait_window#misc#hide ();
	  match warning_window#run () with
	    | `YES -> warning_window#misc#hide (); true
	    | `NO | `DELETE_EVENT -> false
	end
	else false)

let main files =

  (* Main window *)
  let w = GWindow.window
    ~wm_class:"CoqIde" ~wm_name:"CoqIde"
    ~allow_grow:true ~allow_shrink:true
    ~width:current.window_width ~height:current.window_height
    ~title:"CoqIde" ()
  in
  (try
     let icon_image = Filename.concat (List.find
       (fun x -> Sys.file_exists (Filename.concat x "coq.png"))
       (Envars.xdg_data_dirs Ideutils.flash_info)) "coq.png" in
     let icon = GdkPixbuf.from_file icon_image in
     w#set_icon (Some icon)
   with _ -> ());

  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  let new_f _ =
    let session = create_session None in
    let index = session_notebook#append_term session in
    !refresh_editor_hook ();
    session_notebook#goto_page index
  in
  let load_f _ =
    match select_file_for_open ~title:"Load file" () with
      | None -> ()
      | Some f -> do_load f
  in
  let save_f _ =
    let current = session_notebook#current_term in
    try
      (match current.analyzed_view#filename with
        | None ->
          begin match select_file_for_save ~title:"Save file" ()
            with
              | None -> ()
              | Some f ->
                if current.analyzed_view#save_as f then begin
                  current.tab_label#set_text (Filename.basename f);
                  flash_info ("File " ^ f ^ " saved")
                end
                else warning ("Save Failed (check if " ^ f ^ " is writable)")
          end
        | Some f ->
          if current.analyzed_view#save f then
            flash_info ("File " ^ f ^ " saved")
          else warning  ("Save Failed (check if " ^ f ^ " is writable)")

      )
    with
      | e -> warning "Save: unexpected error"
  in
  let saveas_f _ =
    let current = session_notebook#current_term in
    try (match current.analyzed_view#filename with
      | None ->
        begin match select_file_for_save ~title:"Save file as" ()
          with
            | None -> ()
            | Some f ->
              if current.analyzed_view#save_as f then begin
                current.tab_label#set_text (Filename.basename f);
                flash_info "Saved"
              end
              else flash_info "Save Failed"
        end
      | Some f ->
        begin match select_file_for_save
            ~dir:(ref (Filename.dirname f))
            ~filename:(Filename.basename f)
            ~title:"Save file as" ()
          with
            | None -> ()
            | Some f ->
              if current.analyzed_view#save_as f then begin
                current.tab_label#set_text (Filename.basename f);
                flash_info "Saved"
              end else flash_info "Save Failed"
        end);
    with e -> flash_info "Save Failed"
  in
  let revert_f {analyzed_view = av} =
    (try
       match av#filename,av#stats with
         | Some f,Some stats ->
           let new_stats = Unix.stat f in
           if new_stats.Unix.st_mtime > stats.Unix.st_mtime
           then av#revert
         | Some _, None -> av#revert
         | _ -> ()
     with _ -> av#revert)
  in
  let export_f kind _ =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
        flash_info "Cannot print: this buffer has no name"
      | Some f ->
        let basef = Filename.basename f in
        let output =
          let basef_we = try Filename.chop_extension basef with _ -> basef in
          match kind with
            | "latex" -> basef_we ^ ".tex"
            | "dvi" | "ps" | "pdf" | "html" -> basef_we ^ "." ^ kind
            | _ -> assert false
        in
        let cmd =
          local_cd f ^ current.cmd_coqdoc ^ " --" ^ kind ^
	    " -o " ^ (Filename.quote output) ^ " " ^ (Filename.quote basef)
        in
        let s,_ = CUnix.run_command Ideutils.try_convert av#insert_message cmd in
        flash_info (cmd ^
                      if s = Unix.WEXITED 0
                      then " succeeded"
                      else " failed")
  in
  let quit_f _ = if not (forbid_quit_to_save ()) then exit 0 in
  let emit_to_focus sgn =
    let focussed_widget = GtkWindow.Window.get_focus w#as_window in
    let obj = Gobject.unsafe_cast focussed_widget in
    try GtkSignal.emit_unit obj sgn
    with _ -> ()
  in

(* begin Preferences *)
  let reset_revert_timer () =
    disconnect_revert_timer ();
    if current.global_auto_revert then
      revert_timer := Some
	(GMain.Timeout.add ~ms:current.global_auto_revert_delay
	   ~callback:
	   (fun () ->
            List.iter (fun p -> do_if_not_computing p "revert" (fun _ -> sync revert_f p)) session_notebook#pages;
	     true))
  in reset_revert_timer (); (* to enable statup preferences timer *)
  (* XXX *)
  let auto_save_f {analyzed_view = av} =
    (try
       av#auto_save
     with _ -> ())
  in

  let reset_auto_save_timer () =
    disconnect_auto_save_timer ();
    if current.auto_save then
      auto_save_timer := Some
	(GMain.Timeout.add ~ms:current.auto_save_delay
	   ~callback:
	   (fun () ->
	     List.iter (fun p -> do_if_not_computing p "autosave" (fun _ -> sync auto_save_f p)) session_notebook#pages;
	     true))
  in reset_auto_save_timer (); (* to enable statup preferences timer *)
(* end Preferences *)

  let do_or_activate f () =
    let p = session_notebook#current_term in
    do_if_not_computing p "do_or_activate"
      (fun handle ->
        let av = p.analyzed_view in
        ignore (f handle av);
        pop_info ();
        let msg = match Coq.status handle with
        | Interface.Fail (l, str) ->
          "Oops, problem while fetching coq status."
        | Interface.Good status | Interface.Unsafe status ->
          let path = match status.Interface.status_path with
          | [] | _ :: [] -> "" (* Drop the topmost level, usually "Top" *)
          | _ :: l -> " in " ^ String.concat "." l
          in
          let name = match status.Interface.status_proofname with
          | None -> ""
          | Some n -> ", proving " ^ n
          in
          "Ready" ^ path ^ name
        in
        push_info msg
      )
  in
  let do_if_active f () =
    let p = session_notebook#current_term in
    do_if_not_computing p "do_if_active"
      (fun handle -> ignore (f handle p.analyzed_view))
  in
  let match_callback _ =
    let w = get_current_word () in
    let coqtop = session_notebook#current_term.toplvl in
    try
      Coq.try_grab coqtop begin fun handle -> match Coq.mkcases handle w with
        | Interface.Fail _ -> raise Not_found
        | Interface.Good cases | Interface.Unsafe cases ->
          let print_branch c l =
	    Format.fprintf c " | @[<hov 1>%a@]=> _@\n"
	      (print_list (fun c s -> Format.fprintf c "%s@ " s)) l
          in
          let b = Buffer.create 1024 in
          let fmt = Format.formatter_of_buffer b in
          Format.fprintf fmt "@[match var with@\n%aend@]@."
            (print_list print_branch) cases;
          let s = Buffer.contents b in
          Minilib.log s;
          let {script = view } = session_notebook#current_term in
          ignore (view#buffer#delete_selection ());
          let m = view#buffer#create_mark
            (view#buffer#get_iter `INSERT)
          in
          if view#buffer#insert_interactive s then
            let i = view#buffer#get_iter (`MARK m) in
            let _ = i#nocopy#forward_chars 9 in
            view#buffer#place_cursor ~where:i;
            view#buffer#move_mark ~where:(i#backward_chars 3)
              `SEL_BOUND
      end ignore
    with Not_found -> flash_info "Not an inductive type"
  in
(* External command callback *)
  let compile_f _ =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    save_f ();
    match av#filename with
      | None ->
	flash_info "Active buffer has no name"
      | Some f ->
	let cmd = current.cmd_coqc ^ " -I "
	  ^ (Filename.quote (Filename.dirname f))
	  ^ " " ^ (Filename.quote f) in
	let s,res = CUnix.run_command Ideutils.try_convert av#insert_message cmd in
	if s = Unix.WEXITED 0 then
	  flash_info (f ^ " successfully compiled")
	else begin
	  flash_info (f ^ " failed to compile");
	  Coq.try_grab v.toplvl av#process_until_end_or_error ignore;
	  av#insert_message "Compilation output:\n";
	  av#insert_message res
	end
  in
  let make_f _ =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
	flash_info "Cannot make: this buffer has no name"
      | Some f ->
	let cmd = local_cd f ^ current.cmd_make in

	(*
	  save_f ();
	*)
	av#insert_message "Command output:\n";
	let s,res = CUnix.run_command Ideutils.try_convert av#insert_message cmd in
	last_make := res;
	last_make_index := 0;
	flash_info (current.cmd_make ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in
  let next_error _ =
    try
      let file,line,start,stop,error_msg = search_next_error () in
      do_load file;
      let v = session_notebook#current_term in
      let av = v.analyzed_view in
      let input_buffer = v.script#buffer in
      (*
	let init = input_buffer#start_iter in
	let i = init#forward_lines (line-1) in
      *)
      (*
	let convert_pos = byte_offset_to_char_offset phrase in
	let start = convert_pos start in
	let stop = convert_pos stop in
      *)
      (*
	let starti = i#forward_chars start in
	let stopi = i#forward_chars stop in
      *)
      let starti = input_buffer#get_iter_at_byte ~line:(line-1) start in
      let stopi = input_buffer#get_iter_at_byte ~line:(line-1) stop in
      input_buffer#apply_tag Tags.Script.error
	~start:starti
	~stop:stopi;
      input_buffer#place_cursor ~where:starti;
      av#set_message error_msg;
      v.script#misc#grab_focus ()
    with Not_found ->
      last_make_index := 0;
      let v = session_notebook#current_term in
      let av = v.analyzed_view in
      av#set_message "No more errors.\n"
  in
  let coq_makefile_f _ =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
	flash_info "Cannot make makefile: this buffer has no name"
      | Some f ->
	let cmd = local_cd f ^ current.cmd_coqmakefile in
	let s,res = CUnix.run_command Ideutils.try_convert av#insert_message cmd in
	flash_info
	  (current.cmd_coqmakefile ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in

  let file_actions = GAction.action_group ~name:"File" () in
  let edit_actions = GAction.action_group ~name:"Edit" () in
  let view_actions = GAction.action_group ~name:"View" () in
  let export_actions = GAction.action_group ~name:"Export" () in
  let navigation_actions = GAction.action_group ~name:"Navigation" () in
  let tactics_actions = GAction.action_group ~name:"Tactics" () in
  let templates_actions = GAction.action_group ~name:"Templates" () in
  let queries_actions = GAction.action_group ~name:"Queries" () in
  let compile_actions = GAction.action_group ~name:"Compile" () in
  let windows_actions = GAction.action_group ~name:"Windows" () in
  let help_actions = GAction.action_group ~name:"Help" () in
  let add_gen_actions menu_name act_grp l =
    let no_under = Util.string_map (fun x -> if x = '_' then '-' else x) in
    let add_simple_template menu_name act_grp text =
      let text' =
	let l = String.length text - 1 in
	if String.get text l = '.'
	then text ^"\n"
	else text ^" "
      in
      GAction.add_action (menu_name^" "^(no_under text)) ~label:text
	~callback:(fun _ -> let {script = view } = session_notebook#current_term in
			    ignore (view#buffer#insert_interactive text')) act_grp
    in
    List.iter (function
      | [] -> ()
      | [s] -> add_simple_template menu_name act_grp s
      | s::_ as ll -> let label = "_@..." in label.[1] <- s.[0];
		      GAction.add_action (menu_name^" "^(String.make 1 s.[0])) ~label act_grp;
		      List.iter (add_simple_template menu_name act_grp) ll
    ) l
  in
  let tactic_shortcut s sc = GAction.add_action s ~label:("_"^s)
    ~accel:(current.modifier_for_tactics^sc)
    ~callback:(fun _ -> do_if_active (fun handle a -> a#tactic_wizard handle [s]) ()) in
  let query_searchabout () =
    let word = get_current_word () in
    let term = session_notebook#current_term in
    let query handle =
      let results = Coq.search handle [Interface.SubType_Pattern word, true] in
      let results = match results with | Interface.Good l -> l | _ -> [] in
      let buf =  term.message_view#buffer in
      let insert result =
        let basename = result.Interface.search_answer_base_name in
        let path = result.Interface.search_answer_full_path in
        let name = String.concat "." path ^ "." ^ basename in
        let tpe = result.Interface.search_answer_type in
        buf#insert ~tags:[Tags.Message.item] name;
        buf#insert "\n";
        buf#insert tpe;
        buf#insert "\n";
      in
      term.message_view#clear ();
      List.iter insert results
    in
    Coq.try_grab term.toplvl query ignore
  in
  let query_callback command _ =
    let word = get_current_word () in
    let term = session_notebook#current_term in
    let f query handle = term.analyzed_view#raw_coq_query handle query in
    if not (word = "") then
      let query = command ^ " " ^ word ^ "." in
      term.message_view#clear ();
      try Coq.try_grab term.toplvl (f query) ignore
      with e -> term.message_view#push Interface.Error (Printexc.to_string e)
  in
  let query_callback command _ =
    if command = "SearchAbout" then query_searchabout () else query_callback command ()
  in
  let query_shortcut s accel =
    GAction.add_action s ~label:("_"^s) ?accel ~callback:(query_callback s)
  in
  let add_complex_template (name, label, text, offset, len, key) =
    (* Templates/Lemma *)
    let callback _ =
      let {script = view } = session_notebook#current_term in
      if view#buffer#insert_interactive text then begin
	let iter = view#buffer#get_iter_at_mark `INSERT in
	ignore (iter#nocopy#backward_chars offset);
	view#buffer#move_mark `INSERT ~where:iter;
	ignore (iter#nocopy#backward_chars len);
	view#buffer#move_mark `SEL_BOUND ~where:iter;
      end in
      match key with
	|Some ac -> GAction.add_action name ~label ~callback ~accel:(current.modifier_for_templates^ac)
	|None -> GAction.add_action name ~label ~callback ?accel:None
  in
    GAction.add_actions file_actions [
      GAction.add_action "File" ~label:"_File";
      GAction.add_action "New" ~callback:new_f ~stock:`NEW;
      GAction.add_action "Open" ~callback:load_f ~stock:`OPEN;
      GAction.add_action "Save" ~callback:save_f ~stock:`SAVE ~tooltip:"Save current buffer";
      GAction.add_action "Save as" ~label:"S_ave as" ~callback:saveas_f ~stock:`SAVE_AS;
      GAction.add_action "Save all" ~label:"Sa_ve all" ~callback:(fun _ -> saveall_f ());
      GAction.add_action "Revert all buffers" ~label:"_Revert all buffers" ~callback:(fun _ -> List.iter revert_f session_notebook#pages) ~stock:`REVERT_TO_SAVED;
      GAction.add_action "Close buffer" ~label:"_Close buffer" ~callback:(fun _ -> remove_current_view_page ()) ~stock:`CLOSE ~tooltip:"Close current buffer";
      GAction.add_action "Print..." ~label:"_Print..." ~callback:(fun _ -> do_print session_notebook#current_term) ~stock:`PRINT ~accel:"<Ctrl>p";
      GAction.add_action "Rehighlight" ~label:"Reh_ighlight" ~accel:"<Ctrl>l"
	~callback:(fun _ -> force_retag
                     session_notebook#current_term.script#buffer;
		     session_notebook#current_term.analyzed_view#recenter_insert)
	~stock:`REFRESH;
      GAction.add_action "Quit" ~callback:quit_f ~stock:`QUIT;
    ];
    GAction.add_actions export_actions [
      GAction.add_action "Export to" ~label:"E_xport to";
      GAction.add_action "Html" ~label:"_Html" ~callback:(export_f "html");
      GAction.add_action "Latex" ~label:"_LaTeX" ~callback:(export_f "latex");
      GAction.add_action "Dvi" ~label:"_Dvi" ~callback:(export_f "dvi");
      GAction.add_action "Pdf" ~label:"_Pdf" ~callback:(export_f "pdf");
      GAction.add_action "Ps" ~label:"_Ps" ~callback:(export_f "ps");
    ];
    GAction.add_actions edit_actions [
      GAction.add_action "Edit" ~label:"_Edit";
      GAction.add_action "Undo" ~accel:"<Ctrl>u"
	~callback:(fun _ ->
                     let term = session_notebook#current_term in
                     do_if_not_computing term "undo"
		     (fun handle ->
			ignore (term.script#undo ()))) ~stock:`UNDO;
      GAction.add_action "Redo" ~stock:`REDO
	~callback:(fun _ -> ignore (session_notebook#current_term.script#redo ()));
      GAction.add_action "Cut"
        ~callback:(fun _ -> emit_to_focus GtkText.View.S.cut_clipboard) ~stock:`CUT;
      GAction.add_action "Copy"
        ~callback:(fun _ -> emit_to_focus GtkText.View.S.copy_clipboard) ~stock:`COPY;
      GAction.add_action "Paste"
        ~callback:(fun _ -> emit_to_focus GtkText.View.S.paste_clipboard) ~stock:`PASTE;
      GAction.add_action "Find" ~stock:`FIND
        ~callback:(fun _ -> session_notebook#current_term.finder#show `FIND);
      GAction.add_action "Find Next" ~label:"Find _Next" ~stock:`GO_DOWN ~accel:"F3"
        ~callback:(fun _ -> session_notebook#current_term.finder#find_forward ());
      GAction.add_action "Find Previous" ~label:"Find _Previous" ~stock:`GO_UP ~accel:"<Shift>F3"
        ~callback:(fun _ -> session_notebook#current_term.finder#find_backward ());
      GAction.add_action "Replace" ~stock:`FIND_AND_REPLACE
        ~callback:(fun _ -> session_notebook#current_term.finder#show `REPLACE);
     GAction.add_action "Close Find" ~accel:"Escape"
        ~callback:(fun _ -> session_notebook#current_term.finder#hide ());
      GAction.add_action "Complete Word" ~label:"Complete Word" ~callback:(fun _ ->
	     ignore ( ()
(*	       let av = session_notebook#current_term.analyzed_view in
	       av#complete_at_offset (av#get_insert)#offset*)
	     )) ~accel:"<Ctrl>slash";
      GAction.add_action "External editor" ~label:"External editor" ~callback:(fun _ ->
	let av = session_notebook#current_term.analyzed_view in
	match av#filename with
	  | None -> warning "Call to external editor available only on named files"
	  | Some f ->
	    save_f ();
	    let com = Util.subst_command_placeholder current.cmd_editor (Filename.quote f) in
	    let _ = CUnix.run_command Ideutils.try_convert av#insert_message com in
	    av#revert) ~stock:`EDIT;
      GAction.add_action "Preferences" ~callback:(fun _ ->
	begin
	  try configure ~apply:update_notebook_pos ()
	  with _ -> flash_info "Cannot save preferences"
	end;
	reset_revert_timer ()) ~accel:"<Ctrl>comma" ~stock:`PREFERENCES;
      (* GAction.add_action "Save preferences" ~label:"_Save preferences" ~callback:(fun _ -> save_pref ()); *) ];
    GAction.add_actions view_actions [
      GAction.add_action "View" ~label:"_View";
      GAction.add_action "Previous tab" ~label:"_Previous tab" ~accel:("<Alt>Left") ~stock:`GO_BACK
        ~callback:(fun _ -> session_notebook#previous_page ());
      GAction.add_action "Next tab" ~label:"_Next tab" ~accel:("<Alt>Right") ~stock:`GO_FORWARD
        ~callback:(fun _ -> session_notebook#next_page ());
      GAction.add_toggle_action "Show Toolbar" ~label:"Show _Toolbar"
        ~active:(current.show_toolbar) ~callback:
        (fun _ -> current.show_toolbar <- not current.show_toolbar;
           !refresh_toolbar_hook ());
      GAction.add_toggle_action "Show Query Pane" ~label:"Show _Query Pane"
        ~callback:(fun _ -> let ccw = session_notebook#current_term.command in
                     if ccw#frame#misc#visible
                     then ccw#frame#misc#hide ()
                     else ccw#frame#misc#show ())
        ~accel:"<Alt>Escape";
    ];
    List.iter
      (fun (opts,name,label,key,dflt) ->
         GAction.add_toggle_action name ~active:dflt ~label
           ~accel:(current.modifier_for_display^key)
          ~callback:(fun v -> do_or_activate (fun handle av ->
            let () = setopts handle opts v#get_active in
            av#show_goals handle) ()) view_actions)
      print_items;
    GAction.add_actions navigation_actions [
      GAction.add_action "Navigation" ~label:"_Navigation";
      GAction.add_action "Forward" ~label:"_Forward" ~stock:`GO_DOWN
	~callback:(fun _ -> do_or_activate (fun handle a -> a#process_next_phrase handle true) ())
	~tooltip:"Forward one command" ~accel:(current.modifier_for_navigation^"Down");
      GAction.add_action "Backward" ~label:"_Backward" ~stock:`GO_UP
	~callback:(fun _ -> do_or_activate (fun handle a -> a#backtrack_last_phrase handle) ())
	~tooltip:"Backward one command" ~accel:(current.modifier_for_navigation^"Up");
      GAction.add_action "Go to" ~label:"_Go to" ~stock:`JUMP_TO
	~callback:(fun _ -> do_or_activate (fun handle a -> a#go_to_insert handle) ())
	~tooltip:"Go to cursor" ~accel:(current.modifier_for_navigation^"Right");
      GAction.add_action "Start" ~label:"_Start" ~stock:`GOTO_TOP
	~callback:(fun _ -> force_reset_initial ())
	~tooltip:"Restart coq" ~accel:(current.modifier_for_navigation^"Home");
      GAction.add_action "End" ~label:"_End" ~stock:`GOTO_BOTTOM
	~callback:(fun _ -> do_or_activate (fun handle a -> a#process_until_end_or_error handle) ())
	~tooltip:"Go to end" ~accel:(current.modifier_for_navigation^"End");
      GAction.add_action "Interrupt" ~label:"_Interrupt" ~stock:`STOP
	~callback:(fun _ -> break ()) ~tooltip:"Interrupt computations"
	~accel:(current.modifier_for_navigation^"Break");
(* wait for this available in GtkSourceView !
      GAction.add_action "Hide" ~label:"_Hide" ~stock:`MISSING_IMAGE
	~callback:(fun _ -> let sess = session_notebook#current_term in
		     toggle_proof_visibility sess.script#buffer
		       sess.analyzed_view#get_insert) ~tooltip:"Hide proof"
	~accel:(current.modifier_for_navigation^"h");*)
      GAction.add_action "Previous" ~label:"_Previous" ~stock:`GO_BACK
	~callback:(fun _ -> do_or_activate (fun _ a -> a#go_to_prev_occ_of_cur_word) ())
	~tooltip:"Previous occurence" ~accel:(current.modifier_for_navigation^"less");
      GAction.add_action "Next" ~label:"_Next" ~stock:`GO_FORWARD
	~callback:(fun _ -> do_or_activate (fun _ a -> a#go_to_next_occ_of_cur_word) ())
	~tooltip:"Next occurence" ~accel:(current.modifier_for_navigation^"greater");
    ];
    GAction.add_actions tactics_actions [
      GAction.add_action "Try Tactics" ~label:"_Try Tactics";
      GAction.add_action "Wizard" ~tooltip:"Proof Wizard" ~label:"<Proof Wizard>"
	~stock:`DIALOG_INFO ~callback:(fun _ -> do_if_active (fun handle a -> a#tactic_wizard handle
						       current.automatic_tactics) ())
	~accel:(current.modifier_for_tactics^"dollar");
      tactic_shortcut "auto" "a";
      tactic_shortcut "auto with *" "asterisk";
      tactic_shortcut "eauto" "e";
      tactic_shortcut "eauto with *" "ampersand";
      tactic_shortcut "intuition" "i";
      tactic_shortcut "omega" "o";
      tactic_shortcut "simpl" "s";
      tactic_shortcut "tauto" "p";
      tactic_shortcut "trivial" "v";
    ];
    add_gen_actions "Tactic" tactics_actions Coq_commands.tactics;
    GAction.add_actions templates_actions [
      GAction.add_action "Templates" ~label:"Te_mplates";
      add_complex_template
	("Lemma", "_Lemma __", "Lemma new_lemma : .\nProof.\n\nSave.\n",
	 19, 9, Some "L");
      add_complex_template
	("Theorem", "_Theorem __", "Theorem new_theorem : .\nProof.\n\nSave.\n",
	 19, 11, Some "T");
      add_complex_template
	("Definition", "_Definition __", "Definition ident := .\n",
	 6, 5, Some "D");
      add_complex_template
	("Inductive", "_Inductive __", "Inductive ident : :=\n  | : .\n",
	 14, 5, Some "I");
      add_complex_template
	("Fixpoint", "_Fixpoint __", "Fixpoint ident (_ : _) {struct _} : _ :=\n.\n",
	 29, 5, Some "F");
      add_complex_template ("Scheme", "_Scheme __",
			    "Scheme new_scheme := Induction for _ Sort _\
\nwith _ := Induction for _ Sort _.\n",61,10, Some "S");
      GAction.add_action "match" ~label:"match ..." ~callback:match_callback
	~accel:(current.modifier_for_templates^"C");
    ];
    add_gen_actions "Template" templates_actions Coq_commands.commands;
    GAction.add_actions queries_actions [
      GAction.add_action "Queries" ~label:"_Queries";
      query_shortcut "SearchAbout" (Some "F2");
      query_shortcut "Check" (Some "F3");
      query_shortcut "Print" (Some "F4");
      query_shortcut "About" (Some "F5");
      query_shortcut "Locate" None;
      query_shortcut "Whelp Locate" None;
    ];
    GAction.add_actions compile_actions [
      GAction.add_action "Compile" ~label:"_Compile";
      GAction.add_action "Compile buffer" ~label:"_Compile buffer" ~callback:compile_f;
      GAction.add_action "Make" ~label:"_Make" ~callback:make_f ~accel:"F6";
      GAction.add_action "Next error" ~label:"_Next error" ~callback:next_error
	~accel:"F7";
      GAction.add_action "Make makefile" ~label:"Make makefile" ~callback:coq_makefile_f;
    ];
    GAction.add_actions windows_actions [
      GAction.add_action "Windows" ~label:"_Windows";
      GAction.add_action "Detach View" ~label:"Detach _View"
	~callback:(fun _ -> let p = session_notebook#current_term in
                     do_if_not_computing p "detach view"
		     (function handle ->
			let w = GWindow.window ~show:true
			  ~width:(current.window_width*2/3)
			  ~height:(current.window_height*2/3)
			  ~position:`CENTER
			  ~title:(match p.analyzed_view#filename with
				    | None -> "*Unnamed*"
				    | Some f -> f)
			  ()
			in
			let sb = GBin.scrolled_window
			  ~packing:w#add ()
			in
			let nv = GText.view
			  ~buffer:p.script#buffer
			  ~packing:sb#add
			  ()
			in
			  nv#misc#modify_font
			    current.text_font;
			  ignore (w#connect#destroy
				    ~callback:
				    (fun () -> p.analyzed_view#remove_detached_view w));
			  p.analyzed_view#add_detached_view w));
    ];
    GAction.add_actions help_actions [
      GAction.add_action "Help" ~label:"_Help";
      GAction.add_action "Browse Coq Manual" ~label:"Browse Coq _Manual"
	~callback:(fun _ ->
		     let av = session_notebook#current_term.analyzed_view in
		       browse av#insert_message (doc_url ()));
      GAction.add_action "Browse Coq Library" ~label:"Browse Coq _Library"
	~callback:(fun _ ->
		     let av = session_notebook#current_term.analyzed_view in
		       browse av#insert_message current.library_url);
      GAction.add_action "Help for keyword" ~label:"Help for _keyword"
	~callback:(fun _ -> let av = session_notebook#current_term.analyzed_view in
		     av#help_for_keyword ()) ~stock:`HELP;
      GAction.add_action "About Coq" ~label:"_About" ~stock:`ABOUT;
    ];
    Coqide_ui.init ();
    Coqide_ui.ui_m#insert_action_group file_actions 0;
    Coqide_ui.ui_m#insert_action_group export_actions 0;
    Coqide_ui.ui_m#insert_action_group edit_actions 0;
    Coqide_ui.ui_m#insert_action_group view_actions 0;
    Coqide_ui.ui_m#insert_action_group navigation_actions 0;
    Coqide_ui.ui_m#insert_action_group tactics_actions 0;
    Coqide_ui.ui_m#insert_action_group templates_actions 0;
    Coqide_ui.ui_m#insert_action_group queries_actions 0;
    Coqide_ui.ui_m#insert_action_group compile_actions 0;
    Coqide_ui.ui_m#insert_action_group windows_actions 0;
    Coqide_ui.ui_m#insert_action_group help_actions 0;
    w#add_accel_group Coqide_ui.ui_m#get_accel_group ;
    GtkMain.Rc.parse_string "gtk-can-change-accels = 1";
    if Coq_config.gtk_platform <> `QUARTZ
    then vbox#pack (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar");
    let tbar = GtkButton.Toolbar.cast ((Coqide_ui.ui_m#get_widget "/CoqIde ToolBar")#as_widget)
    in let () = GtkButton.Toolbar.set ~orientation:`HORIZONTAL ~style:`ICONS
	~tooltips:true tbar in
    let toolbar = new GObj.widget tbar in
    vbox#pack toolbar;

    ignore (w#event#connect#delete ~callback:(fun _ -> quit_f (); true));

  (* Reset on tab switch *)
  ignore (session_notebook#connect#switch_page
    (fun _ -> if current.reset_on_tab_switch then force_reset_initial ()));
  (* The vertical Separator between Scripts and Goals *)
  vbox#pack ~expand:true session_notebook#coerce;
  update_notebook_pos ();
  let lower_hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
  lower_hbox#pack ~expand:true status#coerce;
  push_info "Ready";
  (* Location display *)
  let l = GMisc.label
    ~text:"Line:     1 Char:   1"
    ~packing:lower_hbox#pack () in
  l#coerce#misc#set_name "location";
  set_location := l#set_text;
  (* Progress Bar *)
  lower_hbox#pack pbar#coerce;
  pbar#set_text "CoqIde started";

  (* Initializing hooks *)

  refresh_toolbar_hook :=
    (fun () -> if current.show_toolbar then toolbar#misc#show () else toolbar#misc#hide ());
  refresh_style_hook :=
    (fun () ->
      let style =  style_manager#style_scheme current.source_style in
      let iter_page p = p.script#source_buffer#set_style_scheme style in
      List.iter iter_page session_notebook#pages;
    );
  refresh_editor_hook :=
    (fun () ->
      let wrap_mode = if current.dynamic_word_wrap then `WORD else `NONE in
      let show_spaces =
        if current.show_spaces then 0b1001011 (* SPACE, TAB, NBSP, TRAILING *)
        else 0
      in
      let fd = current.text_font in
      let clr = Tags.color_of_string current.background_color in

      let iter_page p =
        (* Editor settings *)
        p.script#set_wrap_mode wrap_mode;
        p.script#set_show_line_numbers current.show_line_number;
        p.script#set_auto_indent current.auto_indent;
        p.script#set_highlight_current_line current.highlight_current_line;

        (* Hack to handle missing binding in lablgtk *)
        let conv = { Gobject.name = "draw-spaces"; Gobject.conv = Gobject.Data.int } in
        Gobject.set conv p.script#as_widget show_spaces;

        p.script#set_show_right_margin current.show_right_margin;
        p.script#set_insert_spaces_instead_of_tabs current.spaces_instead_of_tabs;
        p.script#set_tab_width current.tab_length;
        p.script#set_auto_complete current.auto_complete;

        (* Fonts *)
        p.script#misc#modify_font fd;
        p.proof_view#misc#modify_font fd;
        p.message_view#misc#modify_font fd;
        p.command#refresh_font ();

        (* Colors *)
        p.script#misc#modify_base [`NORMAL, `COLOR clr];
        p.proof_view#misc#modify_base [`NORMAL, `COLOR clr];
        p.message_view#misc#modify_base [`NORMAL, `COLOR clr];
        p.command#refresh_color ()

      in
      List.iter iter_page session_notebook#pages;
    );
  resize_window_hook := (fun () ->
    w#resize
      ~width:current.window_width
      ~height:current.window_height);
  refresh_tabs_hook := update_notebook_pos;

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
    let msg = initial_string ^ version_info in
    session_notebook#current_term.message_view#push Interface.Notice msg
  in

  let about () =
    let dialog = GWindow.about_dialog () in
    let _ = dialog#connect#response (fun _ -> dialog#destroy ()) in
    let _ =
      try
        let image = Filename.concat (List.find
          (fun x -> Sys.file_exists (Filename.concat x "coq.png"))
          (Envars.xdg_data_dirs Ideutils.flash_info)) "coq.png" in
        let startup_image = GdkPixbuf.from_file image in
        dialog#set_logo startup_image
      with _ -> ()
    in
    let copyright = "Coq is developed by the Coq Development Team\n\
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
    ] in
    dialog#set_name "CoqIDE";
    dialog#set_comments "The Coq Integrated Development Environment";
    dialog#set_website Coq_config.wwwcoq;
    dialog#set_version Coq_config.version;
    dialog#set_copyright copyright;
    dialog#set_authors authors;
    dialog#show ()
  in
  (* Remove default pango menu for textviews *)
  w#show ();
  ignore ((help_actions#get_action "About Coq")#connect#activate about);

(* Begin Color configuration *)

  Tags.set_processing_color (Tags.color_of_string current.processing_color);
  Tags.set_processed_color (Tags.color_of_string current.processed_color);

(* End of color configuration *)

  if List.length files >=1 then
    begin
      List.iter (fun f ->
	if Sys.file_exists f then do_load f else
          let f = if Filename.check_suffix f ".v" then f else f^".v" in
	  load_file (fun s -> print_endline s; exit 1) f)
        files;
      session_notebook#goto_page 0;
    end
  else
    begin
      let session = create_session None in
      let index = session_notebook#append_term session in
      !refresh_editor_hook ();
      session_notebook#goto_page index;
    end;
  initial_about ();
  !refresh_toolbar_hook ();
  !refresh_editor_hook ();
  session_notebook#current_term.script#misc#grab_focus ();;

(* This function check every half of second if GeoProof has send
   something on his private clipboard *)

let rec check_for_geoproof_input () =
  let cb_Dr = GData.clipboard (Gdk.Atom.intern "_GeoProof") in
  while true do
    Thread.delay 0.1;
    let s = cb_Dr#text in
    (match s with
	Some s ->
	  if s <> "Ack" then
	    session_notebook#current_term.script#buffer#insert (s^"\n");
	  cb_Dr#set_text "Ack"
      | None -> ()
    );
  (* cb_Dr#clear does not work so i use : *)
  (* cb_Dr#set_text "Ack" *)
  done

(** By default, the coqtop we try to launch is exactly the current coqide
    full name, with the last occurrence of "coqide" replaced by "coqtop".
    This should correctly handle the ".opt", ".byte", ".exe" situations.
    If the replacement fails, we default to "coqtop", hoping it's somewhere
    in the path. Note that the -coqtop option to coqide allows to override
    this default coqtop path *)

let read_coqide_args argv =
  let rec filter_coqtop coqtop project_files out = function
    | "-coqtop" :: prog :: args ->
      if coqtop = None then filter_coqtop (Some prog) project_files out args
      else
       (output_string stderr "Error: multiple -coqtop options"; exit 1)
    | "-f" :: file :: args ->
	filter_coqtop coqtop
	  ((CUnix.canonical_path_name (Filename.dirname file),
	    Project_file.read_project_file file) :: project_files) out args
    | "-f" :: [] -> output_string stderr "Error: missing project file name"; exit 1
    | "-coqtop" :: [] -> output_string stderr "Error: missing argument after -coqtop"; exit 1
    | "-debug"::args -> Minilib.debug := true;
      filter_coqtop coqtop project_files ("-debug"::out) args
    | arg::args -> filter_coqtop coqtop project_files (arg::out) args
    | [] -> (coqtop,List.rev project_files,List.rev out)
  in
  let coqtop,project_files,argv = filter_coqtop None [] [] argv in
    Ideutils.custom_coqtop := coqtop;
    custom_project_files := project_files;
  argv
