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

type direction = Up | Down

type flag = [ `COMMENT | `UNSAFE ]

type ide_info = {
  start : GText.mark;
  stop : GText.mark;
  flags : flag list;
}

let revert_timer = Ideutils.mktimer ()
let autosave_timer = Ideutils.mktimer ()

let prefs = Preferences.current

let logfile = ref None

class type _analyzed_view =
object
  method filename : string option
  method update_stats : unit
  method changed_on_disk : bool
  method revert : unit
  method auto_save : unit
  method save : string -> bool
  method save_as : string -> bool
  method recenter_insert : unit
  method insert_message : string -> unit
  method set_message : string -> unit
  method find_next_occurrence : direction -> unit
  method help_for_keyword : unit -> unit

  method go_to_insert : Coq.task
  method tactic_wizard : string list -> Coq.task
  method process_next_phrase : Coq.task
  method process_until_end_or_error : Coq.task
  method handle_reset_initial : Coq.reset_kind -> Coq.task
  method raw_coq_query : string -> Coq.task
  method show_goals : Coq.task
  method backtrack_last_phrase : Coq.task
  method include_file_dir_in_path : Coq.task
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
  (* To close the detached views of this script, we call manually
     [destroy] on it, triggering some callbacks in [detach_view].
     In a more modern lablgtk, rather use the page-removed signal ? *)
  s.script#destroy ();
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
  let script_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:script_frame#add () in
  let state_paned = GPack.paned `VERTICAL
    ~packing:eval_paned#add2 () in
  let proof_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add1 () in
  let proof_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:proof_frame#add () in
  let message_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add2 () in
  let message_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:message_frame#add () in
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
       fun {Gtk.width=paned_width;Gtk.height=paned_height} ->
         if !old_paned_width <> paned_width ||
            !old_paned_height <> paned_height
         then begin
           eval_paned#set_position
             (eval_paned#position * paned_width / !old_paned_width);
           state_paned#set_position
             (state_paned#position * paned_height / !old_paned_height);
           old_paned_width := paned_width;
           old_paned_height := paned_height;
	 end)
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

let current_view () = session_notebook#current_term.analyzed_view
let current_buffer () = session_notebook#current_term.script#buffer

let cb = GData.clipboard Gdk.Atom.primary

let update_notebook_pos () =
  let pos = match prefs.vertical_tabs, prefs.opposite_tabs with
    | false, false -> `TOP
    | false, true  -> `BOTTOM
    | true , false -> `LEFT
    | true , true  -> `RIGHT
  in
  session_notebook#set_tab_pos pos

exception Unsuccessful

let force_reset_initial () =
  Minilib.log "Reset Initial";
  Coq.reset_coqtop session_notebook#current_term.toplvl

let break () =
  Minilib.log "User break received";
  Coq.break_coqtop session_notebook#current_term.toplvl

let warn_image =
  let img = GMisc.image () in
  img#set_stock `DIALOG_WARNING;
  img#set_icon_size `DIALOG;
  img#coerce

let warning msg =
  GToolbox.message_box ~title:"Warning" ~icon:warn_image msg

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
  ([Opt.all_basic;Opt.existential;Opt.universes],
   "Display all low-level contents", "Display all _low-level contents",
   "l",false)
]

let get_current_word () = match cb#text with
  |Some t -> Minilib.log ("get_current_word : selection = " ^ t); t
  |None ->
    Minilib.log "get_current_word : none selected";
    let b = current_buffer () in
    let it = b#get_iter_at_mark `INSERT in
    let start = find_word_start it in
    let stop = find_word_end start in
    b#move_mark `SEL_BOUND ~where:start;
    b#move_mark `INSERT ~where:stop;
    b#get_text ~slice:true ~start ~stop ()

(** Cut a part of the buffer in sentences and tag them.
    Invariant: either this slice ends the buffer, or it ends with ".".
    May raise [Coq_lex.Unterminated] when the zone ends with
    an unterminated sentence. *)

let split_slice_lax (buffer: GText.buffer) start stop =
  buffer#remove_tag ~start ~stop Tags.Script.comment_sentence;
  buffer#remove_tag ~start ~stop Tags.Script.sentence;
  let slice = buffer#get_text ~start ~stop () in
  let mkiter =
    (* caveat : partial application with effects *)
    let convert = byte_offset_to_char_offset slice in
    fun off -> start#forward_chars (convert off)
  in
  let apply_tag off tag =
    let start = mkiter off in
    buffer#apply_tag ~start ~stop:start#forward_char tag
  in
  Coq_lex.delimit_sentences apply_tag slice

(** Searching forward and backward a position fulfilling some condition *)

let rec forward_search cond (iter:GText.iter) =
  if iter#is_end || cond iter then iter
  else forward_search cond iter#forward_char

let rec backward_search cond (iter:GText.iter) =
  if iter#is_start || cond iter then iter
  else backward_search cond iter#backward_char

let is_sentence_end s =
  s#has_tag Tags.Script.sentence || s#has_tag Tags.Script.comment_sentence
let is_char s c = s#char = Char.code c

(** Search backward the first character of a sentence, starting at [iter]
    and going at most up to [soi] (meant to be the end of the locked zone).
    Raise [StartError] when no proper sentence start has been found.
    A character following a ending "." is considered as a sentence start
    only if this character is a blank. In particular, when a final "."
    at the end of the locked zone isn't followed by a blank, then this
    non-blank character will be signaled as erroneous in [tag_on_insert] below.
*)

exception StartError

let grab_sentence_start (iter:GText.iter) soi =
  let cond iter =
    if iter#compare soi < 0 then raise StartError;
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
  (* the start of the non-locked zone *)
  let soi = buffer#get_iter_at_mark (`NAME "start_of_input") in
  (* the inserted zone is between [prev_insert] and [insert] *)
  let insert = buffer#get_iter_at_mark `INSERT in
  let prev = buffer#get_iter_at_mark (`NAME "prev_insert") in
  (* [prev] is normally always before [insert] even when deleting.
     Let's check this nonetheless *)
  let prev, insert =
    if insert#compare prev < 0 then insert, prev else prev, insert
  in
  try
    let start = grab_sentence_start prev soi in
    (** The status of "{" "}" as sentence delimiters is too fragile.
        We retag up to the next "." instead. *)
    let stop = grab_ending_dot insert in
    try split_slice_lax buffer start stop
    with Coq_lex.Unterminated ->
      (* This shouldn't happen frequently. Either:
         - we are at eof, with indeed an unfinished sentence.
         - we have just inserted an opening of comment or string.
         - the inserted text ends with a "." that interacts with the "."
           found by [grab_ending_dot] to form a non-ending "..".
         In any case, we retag up to eof, since this isn't that costly. *)
      if not stop#is_end then
        try split_slice_lax buffer start buffer#end_iter
        with Coq_lex.Unterminated -> ()
  with StartError ->
    buffer#apply_tag Tags.Script.error ~start:soi ~stop:soi#forward_char

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
  val mutable last_stats = NoSuchFile
  val mutable last_modification_time = 0.
  val mutable last_auto_save_time = 0.

  val hidden_proofs = Hashtbl.create 32

  method filename = filename

  method update_stats = match filename with
    |Some f -> last_stats <- Ideutils.stat f
    |_ -> ()

  method changed_on_disk = match filename with
    |None -> false
    |Some f -> match Ideutils.stat f, last_stats with
        |MTime cur_mt, MTime last_mt -> cur_mt > last_mt
        |MTime _, (NoSuchFile|OtherError) -> true
        |NoSuchFile, MTime _ ->
          flash_info ("Warning, file not on disk anymore : "^f);
          false
        |_ -> false

  method revert =
    let do_revert f =
      push_info "Reverting buffer";
      try
        Coq.reset_coqtop mycoqtop;
        let b = Buffer.create 1024 in
        Ideutils.read_file f b;
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
    in
    match filename with
      | None -> ()
      | Some f ->
        if not input_buffer#modified then do_revert f
        else
          let answ = GToolbox.question_box
            ~title:"Modified buffer changed on disk"
            ~buttons:["Revert from File";
                      "Overwrite File";
                      "Disable Auto Revert"]
            ~default:0
            ~icon:(stock_to_widget `DIALOG_WARNING)
            "Some unsaved buffers changed on disk"
          in
          match answ with
            | 1 -> do_revert f
            | 2 -> if self#save f then flash_info "Overwritten" else
                flash_info "Could not overwrite file"
            | _ ->
              Minilib.log "Auto revert set to false";
              prefs.global_auto_revert <- false;
              revert_timer.kill ()

  method save f =
    if try_export f (input_buffer#get_text ()) then begin
      filename <- Some f;
      self#update_stats;
      input_buffer#set_modified false;
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
        let base = (fst prefs.auto_save_name) ^
          (Filename.basename f) ^
          (snd prefs.auto_save_name)
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
    if not (Sys.file_exists f) then self#save f
    else
      let answ = GToolbox.question_box ~title:"File exists on disk"
        ~buttons:["Overwrite"; "Cancel";]
        ~default:1
        ~icon:warn_image
        ("File "^f^" already exists")
      in
      match answ with
        | 1 -> self#save f
        | _ -> false

  method insert_message s =
    message_view#push Interface.Notice s

  method set_message s =
    message_view#clear ();
    message_view#push Interface.Notice s

  method private push_message level content =
    message_view#push level content

  method private get_start_of_input =
    input_buffer#get_iter_at_mark (`NAME "start_of_input")

  method private get_insert =
    input_buffer#get_iter_at_mark `INSERT

  method recenter_insert =
    input_view#scroll_to_mark
      ~use_align:false ~yalign:0.75 ~within_margin:0.25 `INSERT

  method help_for_keyword () =
    browse_keyword (self#insert_message) (get_current_word ())

  (* go to the next occurrence of the current word, forward or backward *)
  method find_next_occurrence dir =
    let b = input_buffer in
    let start = find_word_start self#get_insert in
    let stop = find_word_end start in
    let text = b#get_text ~start ~stop () in
    let search =
      if dir=Down then stop#forward_search else start#backward_search
    in
    match search text with
      | None -> ()
      | Some(start, _) ->
        (b#place_cursor start;
         self#recenter_insert)

  method show_goals h k =
    Coq.PrintOpt.set_printing_width proof_view#width;
    Coq.goals h (function
      |Interface.Fail (l, str) ->
        (self#set_message ("Error in coqtop:\n"^str); k())
      |Interface.Good goals | Interface.Unsafe goals ->
        Coq.evars h (function
          |Interface.Fail (l, str)->
            (self#set_message ("Error in coqtop:\n"^str); k())
          |Interface.Good evs | Interface.Unsafe evs ->
            proof_view#set_goals goals;
            proof_view#set_evars evs;
            proof_view#refresh ();
            k()))

  (* This method is intended to perform stateless commands *)
  method raw_coq_query phrase h k =
    let () = Minilib.log "raw_coq_query starting now" in
    let display_error s =
      if not (Glib.Utf8.validate s) then
        flash_info "This error is so nasty that I can't even display it."
      else self#insert_message s;
    in
    Coq.interp ~logger:self#push_message ~raw:true ~verbose:false phrase h
      (function
        | Interface.Fail (_, err) -> display_error err; k ()
        | Interface.Good msg | Interface.Unsafe msg ->
          self#insert_message msg; k ())

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
        let is_comment =
          stop#backward_char#has_tag Tags.Script.comment_sentence
        in
        let payload = {
          start = `MARK (input_buffer#create_mark start);
          stop = `MARK (input_buffer#create_mark stop);
          flags = if is_comment then [`COMMENT] else [];
        } in
        Queue.push payload queue;
        if not stop#is_end then loop (succ len) stop
    in
    try loop 0 self#get_start_of_input with Exit -> ()

  method private discard_command_queue queue =
    while not (Queue.is_empty queue) do
      let sentence = Queue.pop queue in
      let start = input_buffer#get_iter_at_mark sentence.start in
      let stop = input_buffer#get_iter_at_mark sentence.stop in
      input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
      input_buffer#delete_mark sentence.start;
      input_buffer#delete_mark sentence.stop;
    done

  method private commit_queue_transaction queue sentence newflags =
    (* A queued command has been successfully done, we push it to [cmd_stack].
       We reget the iters here because Gtk is unable to warranty that they
       were not modified meanwhile. Not really necessary but who knows... *)
    let start = input_buffer#get_iter_at_mark sentence.start in
    let stop = input_buffer#get_iter_at_mark sentence.stop in
    let sentence = { sentence with flags = newflags @ sentence.flags } in
    let tag =
      if List.mem `UNSAFE newflags then Tags.Script.unjustified
      else Tags.Script.processed
    in
    input_buffer#move_mark ~where:stop (`NAME "start_of_input");
    input_buffer#apply_tag tag ~start ~stop;
    input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
    ignore (Queue.pop queue);
    Stack.push sentence cmd_stack

  method private process_error queue phrase loc msg h k =
    let position_error = function
      | None -> ()
      | Some (start, stop) ->
        let soi = self#get_start_of_input in
        let start =
          soi#forward_chars (byte_offset_to_char_offset phrase start) in
        let stop =
          soi#forward_chars (byte_offset_to_char_offset phrase stop) in
        input_buffer#apply_tag Tags.Script.error ~start ~stop;
        input_buffer#place_cursor ~where:start
    in
    self#discard_command_queue queue;
    pop_info ();
    position_error loc;
    message_view#clear ();
    message_view#push Interface.Error msg;
    self#show_goals h k

  (** Compute the phrases until [until] returns [true]. *)
  method private process_until until verbose h k =
    let queue = Queue.create () in
    (* Lock everything and fill the waiting queue *)
    push_info "Coq is computing";
    message_view#clear ();
    input_view#set_editable false;
    self#fill_command_queue until queue;
    (* Now unlock and process asynchronously *)
    input_view#set_editable true;
    let push_info lvl msg = if verbose then self#push_message lvl msg
    in
    Minilib.log "Begin command processing";
    let rec loop () =
      if Queue.is_empty queue then
        let () = pop_info () in
        let () = self#recenter_insert in
        self#show_goals h k
      else
        let sentence = Queue.peek queue in
        if List.mem `COMMENT sentence.flags then
          (self#commit_queue_transaction queue sentence []; loop ())
        else
          (* If the line is not a comment, we interpret it. *)
          let start = input_buffer#get_iter_at_mark sentence.start in
          let stop = input_buffer#get_iter_at_mark sentence.stop in
          let phrase = start#get_slice ~stop in
          let commit_and_continue msg flags =
            push_info Interface.Notice msg;
            self#commit_queue_transaction queue sentence flags;
            loop ()
          in
          Coq.interp ~logger:push_info ~verbose phrase h
            (function
              |Interface.Good msg -> commit_and_continue msg []
              |Interface.Unsafe msg -> commit_and_continue msg [`UNSAFE]
              |Interface.Fail (loc, msg) ->
                self#process_error queue phrase loc msg h k)
    in
    loop ()

  method process_next_phrase h k =
    let until len start stop = 1 <= len in
    self#process_until until true h
      (fun () -> input_buffer#place_cursor ~where:self#get_start_of_input; k())

  method private process_until_iter iter h k =
    let until len start stop =
      if prefs.stop_before then stop#compare iter > 0
      else start#compare iter >= 0
    in
    self#process_until until false h k

  method process_until_end_or_error h k =
    self#process_until_iter input_buffer#end_iter h k

  (** Clear the command stack until [until] returns [true].
      Returns the number of commands sent to Coqtop to backtrack. *)
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
  method private undo_command_stack n h k =
    Coq.rewind n h (function
      |Interface.Good n | Interface.Unsafe n ->
        let until _ len _ _ = n <= len in
        (* Coqtop requested [n] more ACTUAL backtrack *)
        ignore (self#clear_command_stack until);
        k ()
      |Interface.Fail (l, str) ->
        self#set_message
          ("Error while backtracking: " ^ str ^
           "\nCoqIDE and coqtop may be out of sync," ^
           "you may want to use Restart.");
        k ())

  (** Wrapper around the raw undo command *)
  method private backtrack_until until h k =
    push_info "Coq is undoing";
    message_view#clear ();
    (* Lock everything *)
    input_view#set_editable false;
    let to_undo = self#clear_command_stack until in
    self#undo_command_stack to_undo h
      (fun () -> input_view#set_editable true; pop_info (); k ())

  method private backtrack_to_iter iter h k =
    let until _ _ _ stop = iter#compare stop >= 0 in
    self#backtrack_until until h
      (* We may have backtracked too much: let's replay *)
      (fun () -> self#process_until_iter iter h k)

  method backtrack_last_phrase h k =
    let until len _ _ _ = 1 <= len in
    self#backtrack_until until h
      (fun () ->
        input_buffer#place_cursor ~where:self#get_start_of_input;
        self#show_goals h k)

  method go_to_insert h k =
    let point = self#get_insert in
    if point#compare self#get_start_of_input >= 0
    then self#process_until_iter point h k
    else self#backtrack_to_iter point h k

  method tactic_wizard l h k =
    let insert_phrase phrase tag =
      let stop = self#get_start_of_input in
      let phrase' = if stop#starts_line then phrase else "\n"^phrase in
      input_buffer#insert ~iter:stop phrase';
      tag_on_insert (input_buffer :> GText.buffer);
      let start = self#get_start_of_input in
      input_buffer#move_mark ~where:stop (`NAME "start_of_input");
      input_buffer#apply_tag tag ~start ~stop;
      if self#get_insert#compare stop <= 0 then
        input_buffer#place_cursor ~where:stop;
      let ide_payload = {
        start = `MARK (input_buffer#create_mark start);
        stop = `MARK (input_buffer#create_mark stop);
        flags = [];
      } in
      Stack.push ide_payload cmd_stack;
      message_view#clear ();
      self#show_goals h k;
    in
    let display_error (loc, s) =
      if not (Glib.Utf8.validate s) then
        flash_info "This error is so nasty that I can't even display it."
      else self#insert_message s
    in
    let try_phrase phrase stop more =
      Minilib.log "Sending to coq now";
      Coq.interp ~verbose:false phrase h
        (function
          |Interface.Fail (l, str) ->
            display_error (l, str);
            self#insert_message ("Unsuccessfully tried: "^phrase);
            more ()
          |Interface.Good msg ->
            self#insert_message msg;
            stop Tags.Script.processed
          |Interface.Unsafe msg ->
            self#insert_message msg;
            stop Tags.Script.unjustified)
    in
    let rec loop l () = match l with
      | [] -> k ()
      | p :: l' ->
        try_phrase ("progress "^p^".") (insert_phrase (p^".")) (loop l')
    in
    loop l ()

  method handle_reset_initial why h k =
    if why = Coq.Unexpected then warning "Coqtop died badly. Resetting.";
    (* clear the stack *)
    while not (Stack.is_empty cmd_stack) do
      let phrase = Stack.pop cmd_stack in
      input_buffer#delete_mark phrase.start;
      input_buffer#delete_mark phrase.stop
    done;
    (* reset the buffer *)
    let start = input_buffer#start_iter in
    let stop = input_buffer#end_iter in
    input_buffer#move_mark ~where:start (`NAME "start_of_input");
    input_buffer#remove_tag Tags.Script.processed ~start ~stop;
    input_buffer#remove_tag Tags.Script.unjustified ~start ~stop;
    input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
    tag_on_insert (input_buffer :> GText.buffer);
    (* clear the views *)
    message_view#clear ();
    proof_view#clear ();
    clear_info ();
    push_info "Restarted";
    (* apply the initial commands to coq *)
    self#include_file_dir_in_path h k;

  method include_file_dir_in_path h k =
    match filename with
      |None -> k ()
      |Some f ->
        let dir = Filename.dirname f in
        Coq.inloadpath dir h (function
          |Interface.Fail (_,s) ->
            self#set_message
              ("Could not determine lodpath, this might lead to problems:\n"^s);
            k ()
          |Interface.Good true |Interface.Unsafe true -> k ()
          |Interface.Good false |Interface.Unsafe false ->
            let cmd = Printf.sprintf "Add LoadPath \"%s\". "  dir in
            Coq.interp cmd h (function
              |Interface.Fail (l,str) ->
                self#set_message ("Couln't add loadpath:\n"^str);
                k ()
              |Interface.Good _ | Interface.Unsafe _ -> k ()))

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
  let _ = input_buffer#connect#insert_text
    ~callback:(fun it s ->
      (* If a #insert happens in the locked zone, we discard it.
         Other solution: always use #insert_interactive and similar *)
      if (it#compare self#get_start_of_input)<0 then
        GtkSignal.stop_emit ();
      if String.length s > 1 then
        let () = Minilib.log "insert_text: Placing cursor" in
        input_buffer#place_cursor ~where:it;
        if String.contains s '\n' then
          let () = Minilib.log "insert_text: Recentering" in
          self#recenter_insert)
  in
  let _ = input_buffer#connect#begin_user_action
    ~callback:(fun () ->
      let where = self#get_insert in
      input_buffer#move_mark (`NAME "prev_insert") ~where;
      let start = self#get_start_of_input in
      let stop = input_buffer#end_iter in
      input_buffer#remove_tag Tags.Script.error ~start ~stop)
  in
  let _ = input_buffer#connect#end_user_action
    ~callback:(fun () ->
      last_modification_time <- Unix.time ();
      tag_on_insert (input_buffer :> GText.buffer))
  in
  let _ = input_buffer#add_selection_clipboard cb
  in
  let _ = input_buffer#connect#after#mark_set
    ~callback:(fun it m ->
      !set_location
        (Printf.sprintf "Line: %5d Char: %3d"
           (self#get_insert#line + 1)
           (self#get_insert#line_offset + 1));
      match GtkText.Mark.get_name m  with
        | Some "insert" -> ()
        | Some s -> Minilib.log (s^" moved")
        | None -> ())
  in ()
end

(** [last_make_buf] contains the output of the last make compilation.
    [last_make] is the same, but as a string, refreshed only when searching
    the next error.
*)

let last_make_buf = Buffer.create 1024
let last_make = ref ""
let last_make_index = ref 0
let last_make_dir = ref ""
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


(**********************************************************************)
(* session creation and primitive handling                            *)
(**********************************************************************)

let create_session file =
  let basename = match file with
    |None -> "*scratch*"
    |Some f -> Glib.Convert.filename_to_utf8 (Filename.basename f)
  in
  let coqtop_args = match file with
    |None -> !sup_args
    |Some the_file ->
      let get_args f = Project_file.args_from_project f
        !custom_project_files prefs.project_file_name
      in
      match prefs.read_project with
	|Ignore_args -> !sup_args
	|Append_args -> get_args the_file @ !sup_args
	|Subst_args -> get_args the_file
  in
  let coqtop = Coq.spawn_coqtop coqtop_args
  in
  let buffer = GSourceView2.source_buffer
    ~tag_table:Tags.Script.table
    ~highlight_matching_brackets:true
    ?language:(lang_manager#language prefs.source_language)
    ?style_scheme:(style_manager#style_scheme prefs.source_style)
    ()
  in
  let _ = buffer#create_mark ~name:"start_of_input" buffer#start_iter in
  let _ = buffer#create_mark ~name:"prev_insert" buffer#start_iter in
  let _ = buffer#place_cursor ~where:buffer#start_iter
  in
  let script = Wg_ScriptView.script_view coqtop ~source_buffer:buffer
    ~show_line_numbers:true ~wrap_mode:`NONE ()
  in
  let _ = script#misc#set_name "ScriptWindow"
  in
  let proof = Wg_ProofView.proof_view () in
  let _ = proof#misc#set_can_focus true in
  let _ =
    GtkBase.Widget.add_events proof#as_widget [`ENTER_NOTIFY;`POINTER_MOTION]
  in
  let message = Wg_MessageView.message_view () in
  let _ = message#misc#set_can_focus true
  in
  let command = new Wg_Command.command_window coqtop in
  let finder = new Wg_Find.finder (script :> GText.view) in
  let view = new analyzed_view script proof message coqtop file in
  let _ = Coq.set_reset_handler coqtop view#handle_reset_initial in
  let _ = view#update_stats in
  let _ = Coq.init_coqtop coqtop
    (fun h k ->
      view#include_file_dir_in_path h
        (fun () ->
          let fold accu (opts, _, _, _, dflt) =
            List.fold_left (fun accu opt -> (opt, dflt) :: accu) accu opts
          in
          let options = List.fold_left fold [] print_items in
          Coq.PrintOpt.set options h k))
  in
  { tab_label= GMisc.label ~text:basename ();
    script=script;
    proof_view=proof;
    message_view=message;
    analyzed_view=view;
    toplvl=coqtop;
    command=command;
    finder=finder;
  }

(*********************************************************************)
(* functions called by the user interface                            *)
(*********************************************************************)

(* Nota: using && here has the advantage of working both under win32 and unix.
   If someday we want the main command to be tried even if the "cd" has failed,
   then we should use " ; " under unix but " & " under win32 (cf. #2363).
*)

let local_cd file =
  "cd " ^ Filename.quote (Filename.dirname file) ^ " && "

let pr_exit_status = function
  | Unix.WEXITED 0 -> " succeeded"
  | _ -> " failed"

(** Auxiliary functions for the File operations *)

module FileAux = struct

let load_file ?(maycreate=false) f =
  let f = CUnix.correct_path f (Sys.getcwd ()) in
  try
    Minilib.log "Loading file starts";
    let is_f = CUnix.same_file f in
    let rec search_f i = function
      | [] -> false
      | p :: pages ->
        match p.analyzed_view#filename with
	  | Some fn when is_f fn -> session_notebook#goto_page i; true
          | _ -> search_f (i+1) pages
    in
    if not (search_f 0 session_notebook#pages) then begin
      Minilib.log "Loading: get raw content";
      let b = Buffer.create 1024 in
      if Sys.file_exists f then Ideutils.read_file f b
      else if not maycreate then flash_info ("Load failed: no such file");
      Minilib.log "Loading: convert content";
      let s = do_convert (Buffer.contents b) in
      Minilib.log "Loading: create view";
      let session = create_session (Some f) in
      let index = session_notebook#append_term session in
      session_notebook#goto_page index;
      Minilib.log "Loading: stats";
      session.analyzed_view#update_stats;
      let input_buffer = session.script#buffer in
      Minilib.log "Loading: fill buffer";
      input_buffer#set_text s;
      input_buffer#set_modified false;
      input_buffer#place_cursor ~where:input_buffer#start_iter;
      force_retag input_buffer;
      session.script#clear_undo ();
      !refresh_editor_hook ();
      Minilib.log "Loading: success";
    end
  with e -> flash_info ("Load failed: "^(Printexc.to_string e))

let confirm_save ok =
  if ok then flash_info "Saved" else warning "Save Failed"

let select_and_save ~saveas ?filename current =
  let av = current.analyzed_view in
  let do_save = if saveas then av#save_as else av#save in
  let title = if saveas then "Save file as" else "Save file" in
  match select_file_for_save ~title ?filename () with
    |None -> false
    |Some f ->
      let ok = do_save f in
      confirm_save ok;
      if ok then current.tab_label#set_text (Filename.basename f);
      ok

let check_save ~saveas current =
  try match current.analyzed_view#filename with
    |None -> select_and_save ~saveas current
    |Some f ->
      let ok = current.analyzed_view#save f in
      confirm_save ok;
      ok
  with _ -> warning "Save Failed"; false

exception DontQuit

let check_quit saveall =
  (try save_pref () with _ -> flash_info "Cannot save preferences");
  let is_modified p = p.script#buffer#modified in
  if List.exists is_modified session_notebook#pages then begin
    let answ = GToolbox.question_box ~title:"Quit"
      ~buttons:["Save Named Buffers and Quit";
                "Quit without Saving";
                "Don't Quit"]
      ~default:0
      ~icon:warn_image
      "There are unsaved buffers"
    in
    match answ with
      | 1 -> saveall ()
      | 2 -> ()
      | _ -> raise DontQuit
  end;
  List.iter (fun p -> Coq.close_coqtop p.toplvl) session_notebook#pages

(* For MacOS, just to be sure, we close all coqtops (again?) *)
let close_and_quit () =
  List.iter (fun p -> Coq.close_coqtop p.toplvl) session_notebook#pages;
  Coq.final_countdown ()

let crash_save exitcode =
  Minilib.log "Starting emergency save of buffers in .crashcoqide files";
  let idx =
    let r = ref 0 in
    fun () -> incr r; string_of_int !r
  in
  let save_page p =
    let filename = match p.analyzed_view#filename with
      | None -> "Unnamed_coqscript_" ^ idx () ^ ".crashcoqide"
      | Some f -> f^".crashcoqide"
    in
    try
      if try_export filename (p.script#buffer#get_text ()) then
	Minilib.log ("Saved "^filename)
      else Minilib.log ("Could not save "^filename)
    with _ -> Minilib.log ("Could not save "^filename)
  in
  List.iter save_page session_notebook#pages;
  Minilib.log "End emergency save";
  exit exitcode

end

(** Callbacks for the File menu *)

module File = struct

let newfile _ =
  let session = create_session None in
  let index = session_notebook#append_term session in
  !refresh_editor_hook ();
  session_notebook#goto_page index

let load _ =
  match select_file_for_open ~title:"Load file" () with
    | None -> ()
    | Some f -> FileAux.load_file f

let save _ =
  ignore (FileAux.check_save ~saveas:false session_notebook#current_term)

let saveas _ =
  let current = session_notebook#current_term in
  try
    let filename = current.analyzed_view#filename in
    ignore (FileAux.select_and_save ~saveas:true ?filename current)
  with _ -> warning "Save Failed"

let saveall _ =
  List.iter
    (function {analyzed_view = av} -> match av#filename with
      | None -> ()
      | Some f -> ignore (av#save f))
    session_notebook#pages

let revert_all _ =
  List.iter
    (function {analyzed_view = av} ->
      if av#changed_on_disk then av#revert)
    session_notebook#pages

let quit _ =
  try FileAux.check_quit saveall; Coq.final_countdown ()
  with FileAux.DontQuit -> ()

let close_buffer _ =
  let do_remove () =
    session_notebook#remove_page session_notebook#current_page
  in
  let current = session_notebook#current_term in
  if not current.script#buffer#modified then do_remove ()
  else
    let answ = GToolbox.question_box ~title:"Close"
      ~buttons:["Save Buffer and Close";
                "Close without Saving";
                "Don't Close"]
      ~default:0
      ~icon:warn_image
      "This buffer has unsaved modifications"
    in
    match answ with
      | 1 when FileAux.check_save ~saveas:true current -> do_remove ()
      | 2 -> do_remove ()
      | _ -> ()

let export kind _ =
  let av = current_view () in
  match av#filename with
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
        local_cd f ^ prefs.cmd_coqdoc ^ " --" ^ kind ^ " -o " ^
        (Filename.quote output) ^ " " ^ (Filename.quote basef) ^ " 2>&1"
      in
      av#set_message ("Running: "^cmd);
      let finally st = flash_info (cmd ^ pr_exit_status st)
      in
      run_command av#insert_message finally cmd

let print _ =
  let av = current_view () in
  match av#filename with
    |None -> flash_info "Cannot print: this buffer has no name"
    |Some f_name ->
      let cmd =
        local_cd f_name ^ prefs.cmd_coqdoc ^ " -ps " ^
        Filename.quote (Filename.basename f_name) ^ " | " ^ prefs.cmd_print
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

let highlight _ =
  let trm = session_notebook#current_term in
  force_retag trm.script#buffer;
  trm.analyzed_view#recenter_insert

end

(** Timers *)

let reset_revert_timer () =
  revert_timer.kill ();
  if prefs.global_auto_revert then
    revert_timer.run
      ~ms:prefs.global_auto_revert_delay
      ~callback:(fun () -> File.revert_all (); true)

let reset_autosave_timer () =
  let autosave p = try p.analyzed_view#auto_save with _ -> () in
  let autosave_all () = List.iter autosave session_notebook#pages; true in
  autosave_timer.kill ();
  if prefs.auto_save then
    autosave_timer.run ~ms:prefs.auto_save_delay ~callback:autosave_all

(** Export of functions used in [coqide_main] : *)

let forbid_quit () =
  try FileAux.check_quit File.saveall; false
  with FileAux.DontQuit -> true

let close_and_quit = FileAux.close_and_quit
let crash_save = FileAux.crash_save
let do_load f = FileAux.load_file f

(** Callbacks for external commands *)

module External = struct

let compile _ =
  let v = session_notebook#current_term in
  let av = v.analyzed_view in
  File.save ();
  match av#filename with
    |None -> flash_info "Active buffer has no name"
    |Some f ->
      let cmd = prefs.cmd_coqc ^ " -I " ^ (Filename.quote (Filename.dirname f))
	^ " " ^ (Filename.quote f) ^ " 2>&1"
      in
      let buf = Buffer.create 1024 in
      av#set_message ("Running: "^cmd);
      let display s =
        av#insert_message s;
        Buffer.add_string buf s
      in
      let finally st =
        if st = Unix.WEXITED 0 then
          flash_info (f ^ " successfully compiled")
        else begin
          flash_info (f ^ " failed to compile");
          av#set_message "Compilation output:\n";
          av#insert_message (Buffer.contents buf);
        end
      in
      run_command display finally cmd

let make _ =
  let av = current_view () in
  match av#filename with
    |None -> flash_info "Cannot make: this buffer has no name"
    |Some f ->
      File.saveall ();
      let cmd = local_cd f ^ prefs.cmd_make ^ " 2>&1" in
      av#set_message "Compilation output:\n";
      Buffer.reset last_make_buf;
      last_make := "";
      last_make_index := 0;
      last_make_dir := Filename.dirname f;
      let display s =
        av#insert_message s;
        Buffer.add_string last_make_buf s
      in
      let finally st = flash_info (current.cmd_make ^ pr_exit_status st)
      in
      run_command display finally cmd

let next_error _ =
  try
    let file,line,start,stop,error_msg = search_next_error () in
    FileAux.load_file file;
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    let input_buffer = v.script#buffer in
    let starti = input_buffer#get_iter_at_byte ~line:(line-1) start in
    let stopi = input_buffer#get_iter_at_byte ~line:(line-1) stop in
    input_buffer#apply_tag Tags.Script.error ~start:starti ~stop:stopi;
    input_buffer#place_cursor ~where:starti;
    av#set_message error_msg;
    v.script#misc#grab_focus ()
  with Not_found ->
    last_make_index := 0;
    (current_view ())#set_message "No more errors.\n"

let coq_makefile _ =
  let av = current_view () in
  match av#filename with
    |None -> flash_info "Cannot make makefile: this buffer has no name"
    |Some f ->
      let cmd = local_cd f ^ prefs.cmd_coqmakefile in
      let finally st = flash_info (current.cmd_coqmakefile ^ pr_exit_status st)
      in
      run_command ignore finally cmd

let editor _ =
  let av = current_view () in
  match av#filename with
    |None -> warning "Call to external editor available only on named files"
    |Some f ->
      File.save ();
      let f = Filename.quote f in
      let cmd = Util.subst_command_placeholder prefs.cmd_editor f in
      run_command ignore (fun _ -> av#revert) cmd

end

(** Callbacks for the Navigation menu *)

let update_status h k =
  let display msg = pop_info (); push_info msg
  in
  Coq.status h (function
    |Interface.Fail (l, str) ->
      display "Oops, problem while fetching coq status."; k ()
    |Interface.Good status | Interface.Unsafe status ->
      let path = match status.Interface.status_path with
        | [] | _ :: [] -> "" (* Drop the topmost level, usually "Top" *)
        | _ :: l -> " in " ^ String.concat "." l
      in
      let name = match status.Interface.status_proofname with
        | None -> ""
        | Some n -> ", proving " ^ n
      in
      display ("Ready" ^ path ^ name); k ())

let send_to_coq f =
  let term = session_notebook#current_term in
  let av = term.analyzed_view in
  let info () = Minilib.log ("Coq busy, discarding query") in
  let f h k = f av h (fun () -> update_status h k) in
  Coq.try_grab term.toplvl f info

module Nav = struct
  let forward_one _ = send_to_coq (fun a -> a#process_next_phrase)
  let backward_one _ = send_to_coq (fun a -> a#backtrack_last_phrase)
  let goto _ = send_to_coq (fun a -> a#go_to_insert)
  let restart _ = force_reset_initial ()
  let goto_end _ = send_to_coq (fun a -> a#process_until_end_or_error)
  let interrupt _ = break ()
  let previous_occ _ = (current_view ())#find_next_occurrence Up
  let next_occ _ = (current_view ())#find_next_occurrence Down
end

let tactic_wizard_callback l _ = send_to_coq (fun a -> a#tactic_wizard l)

let printopts_callback opts v =
  let b = v#get_active in
  let opts = List.map (fun o -> (o,b)) opts in
  send_to_coq (fun av h k ->
    Coq.PrintOpt.set opts h
      (fun () -> av#show_goals h k))

(** Templates menu *)

let print_branch c l =
  Format.fprintf c " | @[<hov 1>%a@]=> _@\n"
    (print_list (fun c s -> Format.fprintf c "%s@ " s)) l

let print_branches c cases =
  Format.fprintf c "@[match var with@\n%aend@]@."
    (print_list print_branch) cases

let display_match k = function
  |Interface.Fail _ -> flash_info "Not an inductive type"; k ()
  |Interface.Good cases |Interface.Unsafe cases ->
    let text =
      let buf = Buffer.create 1024 in
      let () = print_branches (Format.formatter_of_buffer buf) cases in
      Buffer.contents buf
    in
    Minilib.log ("match template :\n" ^ text);
    let b = current_buffer () in
    let _ =  b#delete_selection () in
    let m = b#create_mark (b#get_iter_at_mark `INSERT) in
    if b#insert_interactive text then begin
      let i = b#get_iter (`MARK m) in
      let _ = i#nocopy#forward_chars 9 in
      let _ = b#place_cursor ~where:i in
      b#move_mark ~where:(i#backward_chars 3) `SEL_BOUND
    end;
    b#delete_mark (`MARK m);
    k ()

let match_callback _ =
  let w = get_current_word () in
  let coqtop = session_notebook#current_term.toplvl in
  Coq.try_grab coqtop (fun h k -> Coq.mkcases w h (display_match k)) ignore

(** Queries *)

module Query = struct

let searchabout () =
  let word = get_current_word () in
  let term = session_notebook#current_term in
  let buf = term.message_view#buffer in
  let insert result =
    let qualid = result.Interface.coq_object_qualid in
    let name = String.concat "." qualid in
    let tpe = result.Interface.coq_object_object in
    buf#insert ~tags:[Tags.Message.item] name;
    buf#insert "\n";
    buf#insert tpe;
    buf#insert "\n";
  in
  let display_results k r =
    term.message_view#clear ();
    List.iter insert (match r with Interface.Good l -> l | _ -> []);
    k ()
  in
  let launch_query h k =
    Coq.search [Interface.SubType_Pattern word, true] h (display_results k)
  in
  Coq.try_grab term.toplvl launch_query ignore

let otherquery command _ =
  let word = get_current_word () in
  let term = session_notebook#current_term in
  if word <> "" then
    let query = command ^ " " ^ word ^ "." in
    term.message_view#clear ();
    Coq.try_grab term.toplvl (term.analyzed_view#raw_coq_query query) ignore

let query command _ =
  if command = "SearchAbout"
  then searchabout ()
  else otherquery command ()

end

(** Misc *)

module MiscMenu = struct

let detach_view _ =
  (* Open a separate window containing the current buffer *)
  let trm = session_notebook#current_term in
  let file = match trm.analyzed_view#filename with
    |None -> "*scratch*"
    |Some f -> f
  in
  let w = GWindow.window ~show:true ~title:file ~position:`CENTER
    ~width:(prefs.window_width*2/3)
    ~height:(prefs.window_height*2/3)
    ()
  in
  let sb = GBin.scrolled_window ~packing:w#add ()
  in
  let nv = GText.view ~buffer:trm.script#buffer ~packing:sb#add ()
  in
  nv#misc#modify_font prefs.text_font;
  (* If the buffer in the main window is closed, destroy this detached view *)
  ignore (trm.script#connect#destroy ~callback:w#destroy)

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
  session_notebook#current_term.message_view#push Interface.Notice msg

let coq_icon () =
  (* May raise Nof_found *)
  let name = "coq.png" in
  let chk d = Sys.file_exists (Filename.concat d name) in
  let dir = List.find chk (Minilib.coqide_data_dirs ()) in
  Filename.concat dir name

let about _ =
  let dialog = GWindow.about_dialog () in
  let _ = dialog#connect#response (fun _ -> dialog#destroy ()) in
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
    "Hugo Herbelin" ]
  in
  dialog#set_name "CoqIDE";
  dialog#set_comments "The Coq Integrated Development Environment";
  dialog#set_website Coq_config.wwwcoq;
  dialog#set_version Coq_config.version;
  dialog#set_copyright copyright;
  dialog#set_authors authors;
  dialog#show ()

  let comment _ = session_notebook#current_term.script#comment ()
  let uncomment _ = session_notebook#current_term.script#uncomment ()

end

(** Refresh functions *)

let refresh_editor_prefs () =
  let wrap_mode = if prefs.dynamic_word_wrap then `WORD else `NONE in
  let show_spaces =
    if prefs.show_spaces then 0b1001011 (* SPACE, TAB, NBSP, TRAILING *)
    else 0
  in
  let fd = prefs.text_font in
  let clr = Tags.color_of_string prefs.background_color
  in
  let iter_page p =
    (* Editor settings *)
    p.script#set_wrap_mode wrap_mode;
    p.script#set_show_line_numbers prefs.show_line_number;
    p.script#set_auto_indent prefs.auto_indent;
    p.script#set_highlight_current_line prefs.highlight_current_line;

    (* Hack to handle missing binding in lablgtk *)
    let conv = { Gobject.name = "draw-spaces"; Gobject.conv = Gobject.Data.int }
    in
    Gobject.set conv p.script#as_widget show_spaces;

    p.script#set_show_right_margin prefs.show_right_margin;
    p.script#set_insert_spaces_instead_of_tabs
      prefs.spaces_instead_of_tabs;
    p.script#set_tab_width prefs.tab_length;
    p.script#set_auto_complete prefs.auto_complete;

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
  List.iter iter_page session_notebook#pages


(** Wrappers around GAction functions for creating menus *)

let menu = GAction.add_actions
let item = GAction.add_action

(** Toggle items in menus for printing options *)

let toggle_item = GAction.add_toggle_action

let toggle_items menu_name l =
  let f (opts,name,label,key,dflt) =
    toggle_item name ~active:dflt ~label
      ~accel:(prefs.modifier_for_display^key)
      ~callback:(printopts_callback opts)
      menu_name
  in
  List.iter f l

(** Create alphabetical menu items with elements in sub-items.
    [l] is a list of lists, one per initial letter *)

let alpha_items menu_name item_name l =
  let no_under = Util.String.map (fun x -> if x = '_' then '-' else x)
  in
  let mk_item text =
    let text' =
      let last = String.length text - 1 in
      if text.[last] = '.'
      then text ^"\n"
      else text ^" "
    in
    item (item_name^" "^(no_under text)) ~label:text
      ~callback:(fun _ ->
	ignore ((current_buffer ())#insert_interactive text'))
      menu_name
  in
  let mk_items = function
    | [] -> ()
    | [s] -> mk_item s
    | s::_ as ll ->
      let name = item_name^" "^(String.make 1 s.[0]) in
      let label = "_@..." in label.[1] <- s.[0];
      item name ~label menu_name;
      List.iter mk_item ll
  in
  List.iter mk_items l

(** Create a menu item that will insert a given text,
    and select the zone given by (offset,len).
    The first word in the text is used as item keyword.
    Caveat: the offset is now from the start of the text. *)

let template_item (text, offset, len, key) =
  let modifier = prefs.modifier_for_templates in
  let idx = String.index text ' ' in
  let name = String.sub text 0 idx in
  let label = "_"^name^" __" in
  let negoffset = String.length text - offset - len in
  let callback _ =
    let b = current_buffer () in
    if b#insert_interactive text then begin
      let iter = b#get_iter_at_mark `INSERT in
      ignore (iter#nocopy#backward_chars negoffset);
      b#move_mark `INSERT ~where:iter;
      ignore (iter#nocopy#backward_chars len);
      b#move_mark `SEL_BOUND ~where:iter;
    end
  in
  item name ~label ~callback ~accel:(modifier^key)

(** Creation of the main coqide window *)

let build_ui () =
  let w = GWindow.window
    ~wm_class:"CoqIde" ~wm_name:"CoqIde"
    ~allow_grow:true ~allow_shrink:true
    ~width:prefs.window_width ~height:prefs.window_height
    ~title:"CoqIde" ()
  in
  let () =
    try w#set_icon (Some (GdkPixbuf.from_file (MiscMenu.coq_icon ())))
    with _ -> ()
  in
  let _ = w#event#connect#delete ~callback:(fun _ -> File.quit (); true)
  in
  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  let emit_to_focus sgn =
    let focussed_widget = GtkWindow.Window.get_focus w#as_window in
    let obj = Gobject.unsafe_cast focussed_widget in
    try GtkSignal.emit_unit obj sgn
    with _ -> ()
  in

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
      ~callback:File.close_buffer~tooltip:"Close current buffer";
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
      ~callback:(fun _ -> session_notebook#current_term.script#undo ());
    item "Redo" ~stock:`REDO
      ~callback:(fun _ -> session_notebook#current_term.script#redo ());
    item "Cut" ~stock:`CUT
      ~callback:(fun _ -> emit_to_focus GtkText.View.S.cut_clipboard);
    item "Copy" ~stock:`COPY
      ~callback:(fun _ -> emit_to_focus GtkText.View.S.copy_clipboard);
    item "Paste" ~stock:`PASTE
      ~callback:(fun _ -> emit_to_focus GtkText.View.S.paste_clipboard);
    item "Find" ~stock:`FIND
      ~callback:(fun _ -> session_notebook#current_term.finder#show `FIND);
    item "Find Next" ~label:"Find _Next" ~stock:`GO_DOWN ~accel:"F3"
      ~callback:(fun _ -> session_notebook#current_term.finder#find_forward ());
    item "Find Previous" ~label:"Find _Previous" ~stock:`GO_UP
      ~accel:"<Shift>F3"
      ~callback:(fun _ -> session_notebook#current_term.finder#find_backward ());
    item "Replace" ~stock:`FIND_AND_REPLACE
      ~callback:(fun _ -> session_notebook#current_term.finder#show `REPLACE);
    item "Close Find" ~accel:"Escape"
      ~callback:(fun _ -> session_notebook#current_term.finder#hide ());
    item "Complete Word" ~label:"Complete Word" ~accel:"<Ctrl>slash"
      ~callback:(fun _ ->
        ignore ( ()
(*	       let av = session_notebook#current_term.analyzed_view in
	       av#complete_at_offset (av#get_insert)#offset*)
	));
    item "External editor" ~label:"External editor" ~stock:`EDIT
      ~callback:External.editor;
    item "Preferences" ~accel:"<Ctrl>comma" ~stock:`PREFERENCES
      ~callback:(fun _ ->
        begin
	  try configure ~apply:update_notebook_pos ()
	  with _ -> flash_info "Cannot save preferences"
        end;
        reset_revert_timer ());
  ];

  menu view_menu [
    item "View" ~label:"_View";
    item "Previous tab" ~label:"_Previous tab" ~accel:"<Alt>Left"
      ~stock:`GO_BACK
      ~callback:(fun _ -> session_notebook#previous_page ());
    item "Next tab" ~label:"_Next tab" ~accel:"<Alt>Right"
      ~stock:`GO_FORWARD
      ~callback:(fun _ -> session_notebook#next_page ());
    toggle_item "Show Toolbar" ~label:"Show _Toolbar"
      ~active:(prefs.show_toolbar)
      ~callback:(fun _ ->
        prefs.show_toolbar <- not prefs.show_toolbar;
        !refresh_toolbar_hook ());
    toggle_item "Show Query Pane" ~label:"Show _Query Pane"
      ~accel:"<Alt>Escape"
      ~callback:(fun _ ->
        let ccw = session_notebook#current_term.command in
        if ccw#frame#misc#visible
        then ccw#frame#misc#hide ()
        else ccw#frame#misc#show ())
  ];
  toggle_items view_menu print_items;

  menu navigation_menu [
    item "Navigation" ~label:"_Navigation";
    item "Forward" ~label:"_Forward" ~stock:`GO_DOWN ~callback:Nav.forward_one
      ~tooltip:"Forward one command"
      ~accel:(prefs.modifier_for_navigation^"Down");
    item "Backward" ~label:"_Backward" ~stock:`GO_UP ~callback:Nav.backward_one
      ~tooltip:"Backward one command"
      ~accel:(prefs.modifier_for_navigation^"Up");
    item "Go to" ~label:"_Go to" ~stock:`JUMP_TO ~callback:Nav.goto
      ~tooltip:"Go to cursor"
      ~accel:(prefs.modifier_for_navigation^"Right");
    item "Start" ~label:"_Start" ~stock:`GOTO_TOP ~callback:Nav.restart
      ~tooltip:"Restart coq"
      ~accel:(prefs.modifier_for_navigation^"Home");
    item "End" ~label:"_End" ~stock:`GOTO_BOTTOM  ~callback:Nav.goto_end
      ~tooltip:"Go to end"
      ~accel:(prefs.modifier_for_navigation^"End");
    item "Interrupt" ~label:"_Interrupt" ~stock:`STOP ~callback:Nav.interrupt
      ~tooltip:"Interrupt computations"
      ~accel:(prefs.modifier_for_navigation^"Break");
(* wait for this available in GtkSourceView !
      item "Hide" ~label:"_Hide" ~stock:`MISSING_IMAGE
	~callback:(fun _ -> let sess = session_notebook#current_term in
		     toggle_proof_visibility sess.script#buffer
		       sess.analyzed_view#get_insert) ~tooltip:"Hide proof"
	~accel:(prefs.modifier_for_navigation^"h");*)
    item "Previous" ~label:"_Previous" ~stock:`GO_BACK
      ~callback:Nav.previous_occ
      ~tooltip:"Previous occurence"
      ~accel:(prefs.modifier_for_navigation^"less");
    item "Next" ~label:"_Next" ~stock:`GO_FORWARD ~callback:Nav.next_occ
      ~tooltip:"Next occurence"
      ~accel:(prefs.modifier_for_navigation^"greater");
  ];

  let tacitem s sc =
    item s ~label:("_"^s)
      ~accel:(prefs.modifier_for_tactics^sc)
      ~callback:(tactic_wizard_callback [s])
  in
  menu tactics_menu [
    item "Try Tactics" ~label:"_Try Tactics";
    item "Wizard" ~label:"<Proof Wizard>" ~stock:`DIALOG_INFO
      ~tooltip:"Proof Wizard" ~accel:(prefs.modifier_for_tactics^"dollar")
      ~callback:(tactic_wizard_callback prefs.automatic_tactics);
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
    template_item ("Lemma new_lemma : .\nProof.\n\nSave.\n", 6,9, "L");
    template_item ("Theorem new_theorem : .\nProof.\n\nSave.\n", 8,11, "T");
    template_item ("Definition ident := .\n", 11,5, "E");
    template_item ("Inductive ident : :=\n  | : .\n", 10,5, "I");
    template_item ("Fixpoint ident (_ : _) {struct _} : _ :=\n.\n", 9,5, "F");
    template_item ("Scheme new_scheme := Induction for _ Sort _\n" ^
                   "with _ := Induction for _ Sort _.\n", 7,10, "S");
    item "match" ~label:"match ..." ~accel:(prefs.modifier_for_templates^"C")
      ~callback:match_callback
  ];
  alpha_items templates_menu "Template" Coq_commands.commands;

  let qitem s accel = item s ~label:("_"^s) ?accel ~callback:(Query.query s) in
  menu queries_menu [
    item "Queries" ~label:"_Queries";
    qitem "SearchAbout" (Some "F2");
    qitem "Check" (Some "F3");
    qitem "Print" (Some "F4");
    qitem "About" (Some "F5");
    qitem "Locate" None;
    qitem "Print Assumptions" None;
    qitem "Whelp Locate" None;
  ];

  menu tools_menu [
    item "Tools" ~label:"_Tools";
    item "Comment" ~label:"_Comment" ~accel:"<CTRL>D"
      ~callback:MiscMenu.comment;
    item "Uncomment" ~label:"_Uncomment" ~accel:"<CTRL><SHIFT>D"
      ~callback:MiscMenu.uncomment;
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
	let av = session_notebook#current_term.analyzed_view in
	browse av#insert_message (doc_url ()));
    item "Browse Coq Library" ~label:"Browse Coq _Library"
      ~callback:(fun _ ->
	let av = session_notebook#current_term.analyzed_view in
	browse av#insert_message prefs.library_url);
    item "Help for keyword" ~label:"Help for _keyword" ~stock:`HELP
      ~callback:(fun _ ->
        let av = session_notebook#current_term.analyzed_view in
	av#help_for_keyword ());
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

  (* Reset on tab switch *)
  let _ = session_notebook#connect#switch_page ~callback:(fun _ ->
    if prefs.reset_on_tab_switch then force_reset_initial ())
  in

  (* Vertical Separator between Scripts and Goals *)
  let () = vbox#pack ~expand:true session_notebook#coerce in
  let () = update_notebook_pos () in
  let lower_hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
  let () = lower_hbox#pack ~expand:true status#coerce in
  let () = push_info "Ready" in

  (* Location display *)
  let l = GMisc.label
    ~text:"Line:     1 Char:   1"
    ~packing:lower_hbox#pack ()
  in
  let () = l#coerce#misc#set_name "location" in
  let () = set_location := l#set_text in

  (* Progress Bar *)
  let pbar = GRange.progress_bar ~pulse_step:0.2 () in
  let () = lower_hbox#pack pbar#coerce in
  let () = pbar#set_text "CoqIde started" in
  let _ = Glib.Timeout.add ~ms:300 ~callback:(fun () ->
    let curr_coq = session_notebook#current_term.toplvl in
    if Coq.is_computing curr_coq then pbar#pulse ();
    true)
  in

  (* Initializing hooks *)
  let refresh_toolbar () =
    if prefs.show_toolbar
    then toolbar#misc#show ()
    else toolbar#misc#hide ()
  in
  let refresh_style () =
    let style =  style_manager#style_scheme prefs.source_style in
    let iter_page p = p.script#source_buffer#set_style_scheme style in
    List.iter iter_page session_notebook#pages
  in
  let resize_window () =
    w#resize ~width:prefs.window_width ~height:prefs.window_height
  in
  refresh_toolbar ();
  refresh_toolbar_hook := refresh_toolbar;
  refresh_style_hook := refresh_style;
  refresh_editor_hook := refresh_editor_prefs;
  resize_window_hook := resize_window;
  refresh_tabs_hook := update_notebook_pos;

  (* Color configuration *)
  Tags.set_processing_color (Tags.color_of_string prefs.processing_color);
  Tags.set_processed_color (Tags.color_of_string prefs.processed_color);

  (* Showtime ! *)
  w#show ()

let make_file_buffer f =
  let f =
    if Sys.file_exists f || Filename.check_suffix f ".v" then f
    else f^".v"
  in
  FileAux.load_file ~maycreate:true f

let make_scratch_buffer () =
  let session = create_session None in
  let _ = session_notebook#append_term session in
  !refresh_editor_hook ()

let main files =
  build_ui ();
  reset_revert_timer ();
  reset_autosave_timer ();
  (match files with
    | [] -> make_scratch_buffer ()
    | _ -> List.iter make_file_buffer files);
  session_notebook#goto_page 0;
  MiscMenu.initial_about ();
  session_notebook#current_term.script#misc#grab_focus ();
  Minilib.log "End of Coqide.main"

(* This function check every tenth of second if GeoProof has send
   something on his private clipboard *)

let check_for_geoproof_input () =
  let cb_Dr = GData.clipboard (Gdk.Atom.intern "_GeoProof") in
  let handler () = match cb_Dr#text with
    |None -> true
    |Some "Ack" -> true
    |Some s ->
      (current_buffer ())#insert (s^"\n");
      (* cb_Dr#clear does not work so i use : *)
      cb_Dr#set_text "Ack";
      true
  in
  ignore (GMain.Timeout.add ~ms:100 ~callback:handler)

(** By default, the coqtop we try to launch is exactly the current coqide
    full name, with the last occurrence of "coqide" replaced by "coqtop".
    This should correctly handle the ".opt", ".byte", ".exe" situations.
    If the replacement fails, we default to "coqtop", hoping it's somewhere
    in the path. Note that the -coqtop option to coqide allows to override
    this default coqtop path *)

let read_coqide_args argv =
  let rec filter_coqtop coqtop project_files out = function
    |"-coqtop" :: prog :: args ->
      if coqtop = None then filter_coqtop (Some prog) project_files out args
      else (output_string stderr "Error: multiple -coqtop options"; exit 1)
    |"-f" :: file :: args ->
      let d = CUnix.canonical_path_name (Filename.dirname file) in
      let p = Project_file.read_project_file file in
      filter_coqtop coqtop ((d,p) :: project_files) out args
    |"-f" :: [] ->
      output_string stderr "Error: missing project file name"; exit 1
    |"-coqtop" :: [] ->
      output_string stderr "Error: missing argument after -coqtop"; exit 1
    |"-debug"::args ->
      Minilib.debug := true;
      filter_coqtop coqtop project_files ("-debug"::out) args
    |arg::args -> filter_coqtop coqtop project_files (arg::out) args
    |[] -> (coqtop,List.rev project_files,List.rev out)
  in
  let coqtop,project_files,argv = filter_coqtop None [] [] argv in
  Ideutils.custom_coqtop := coqtop;
  custom_project_files := project_files;
  argv

(** * Coqide's handling of signals *)

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
