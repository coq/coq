(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Coq
open Ideutils
open Interface

type flag = [ `COMMENT | `UNSAFE | `PROCESSING | `ERROR ]

module SentenceId : sig

  type sentence = private {
    start : GText.mark;
    stop : GText.mark;
    mutable flags : flag list;
    edit_id : int;
    mutable state_id : Stateid.t option;
  }

  val mk_sentence :
    start:GText.mark -> stop:GText.mark -> flag list -> sentence

  val assign_state_id : sentence -> Stateid.t -> unit
  val set_flags : sentence -> flag list -> unit
  val add_flag : sentence -> flag -> unit
  val remove_flag : sentence -> flag -> unit
  val same_sentence : sentence -> sentence -> bool
  val hidden_edit_id : unit -> int

end = struct

  type sentence = {
    start : GText.mark;
    stop : GText.mark;
    mutable flags : flag list;
    edit_id : int;
    mutable state_id : Stateid.t option;
  }

  let id = ref 0
  let mk_sentence ~start ~stop flags = decr id; {
    start = start;
    stop = stop;
    flags = flags;
    edit_id = !id;
    state_id = None;
  }
  let hidden_edit_id () = decr id; !id

  let assign_state_id s id =
    assert(s.state_id = None);
    assert(id <> Stateid.dummy);
    s.state_id <- Some id
  let set_flags s f = s.flags <- f
  let add_flag s f = s.flags <- CList.add_set f s.flags
  let remove_flag s f = s.flags <- CList.remove f s.flags
  let same_sentence s1 s2 = s1.edit_id = s2.edit_id && s1.state_id = s2.state_id

end
open SentenceId

let prefs = Preferences.current

let log msg : unit task =
  Coq.lift (fun () -> Minilib.log msg)

class type ops =
object
  method go_to_insert : unit task
  method go_to_mark : GText.mark -> unit task
  method tactic_wizard : string list -> unit task
  method process_next_phrase : unit task
  method process_until_end_or_error : unit task
  method handle_reset_initial : Coq.reset_kind -> unit task
  method raw_coq_query : string -> unit task
  method show_goals : unit task
  method backtrack_last_phrase : unit task
  method initialize : unit task
  method join_document : unit task

  method handle_failure : handle_exn_rty -> unit task

  method destroy : unit -> unit
end

class coqops
  (_script:Wg_ScriptView.script_view)
  (_pv:Wg_ProofView.proof_view)
  (_mv:Wg_MessageView.message_view)
  (_ct:Coq.coqtop)
  get_filename =
object(self)
  val script = _script
  val buffer = (_script#source_buffer :> GText.buffer)
  val proof = _pv
  val messages = _mv

  val cmd_stack = Stack.create ()

  val mutable initial_state = Stateid.initial

  val feedbacks : feedback Queue.t = Queue.create ()
  val feedback_timer = Ideutils.mktimer ()

  initializer
    Coq.set_feedback_handler _ct self#enqueue_feedback;
    Wg_Tooltip.set_tooltip_callback (script :> GText.view);
    feedback_timer.Ideutils.run ~ms:250 ~callback:self#process_feedback

  method destroy () =
    feedback_timer.Ideutils.kill ()

  method private get_start_of_input =
    buffer#get_iter_at_mark (`NAME "start_of_input")

  method private get_insert =
    buffer#get_iter_at_mark `INSERT

  method show_goals =
    Coq.PrintOpt.set_printing_width proof#width;
    Coq.bind (Coq.goals ~logger:messages#push ()) (function
    | Fail x -> self#handle_failure x
    | Good goals ->
      Coq.bind (Coq.evars ()) (function
        | Fail x -> self#handle_failure x
        | Good evs ->
          proof#set_goals goals;
          proof#set_evars evs;
          proof#refresh ();
          Coq.return ()
        )
      )

  (* This method is intended to perform stateless commands *)
  method raw_coq_query phrase =
    let action = log "raw_coq_query starting now" in
    let display_error s =
      if not (Glib.Utf8.validate s) then
        flash_info "This error is so nasty that I can't even display it."
      else messages#add s;
    in
    let query =
      Coq.interp ~logger:messages#push ~raw:true ~verbose:false 0 phrase in
    let next = function
    | Fail (_, _, err) -> display_error err; Coq.return () (* XXX*)
    | Good (_, msg) ->
      messages#add msg; Coq.return ()
    in
    Coq.bind (Coq.seq action query) next

  (** [fill_command_queue until q] fills a command queue until the [until]
      condition returns true; it is fed with the number of phrases read and the
      iters enclosing the current sentence. *)
  method private fill_command_queue until queue =
    let rec loop len iter =
      match Sentence.find buffer iter with
      | None -> raise Exit
      | Some (start, stop) ->
        if until len start stop then raise Exit;
        buffer#apply_tag Tags.Script.to_process ~start ~stop;
        (* Check if this is a comment *)
        let is_comment =
          stop#backward_char#has_tag Tags.Script.comment_sentence
        in
        let sentence =
          mk_sentence
            ~start:(`MARK (buffer#create_mark start))
            ~stop:(`MARK (buffer#create_mark stop))
            (if is_comment then [`COMMENT] else []) in
        Queue.push sentence queue;
        if not stop#is_end then loop (succ len) stop
    in
    try loop 0 self#get_start_of_input with Exit -> ()

  method private discard_command_queue queue =
    while not (Queue.is_empty queue) do
      let sentence = Queue.pop queue in
      let start = buffer#get_iter_at_mark sentence.start in
      let stop = buffer#get_iter_at_mark sentence.stop in
      buffer#remove_tag Tags.Script.to_process ~start ~stop;
      buffer#delete_mark sentence.start;
      buffer#delete_mark sentence.stop;
    done

  method private mark_as_needed sentence =
    let start = buffer#get_iter_at_mark sentence.start in
    let stop = buffer#get_iter_at_mark sentence.stop in
    let to_process = Tags.Script.to_process in
    let processed = Tags.Script.processed in
    let unjustified = Tags.Script.unjustified in
    let error_bg = Tags.Script.error_bg in
    let all_tags = [ to_process; processed; unjustified ] in
    let tags =
      (if List.mem `PROCESSING sentence.flags then to_process else
       if List.mem `ERROR sentence.flags then error_bg else
       processed)
      ::
      (if [ `UNSAFE ] = sentence.flags then [unjustified] else [])
    in
    List.iter (fun t -> buffer#remove_tag t ~start ~stop) all_tags;
    List.iter (fun t -> buffer#apply_tag t ~start ~stop) tags

  method private attach_tooltip sentence loc text =
    let start_sentence, stop_sentence, phrase = self#get_sentence sentence in
    let pre_chars, post_chars =
      if Loc.is_ghost loc then 0, String.length phrase else Loc.unloc loc in
    let pre = Ideutils.glib_utf8_pos_to_offset phrase ~off:pre_chars in
    let post = Ideutils.glib_utf8_pos_to_offset phrase ~off:post_chars in
    let start = start_sentence#forward_chars pre in
    let stop = start_sentence#forward_chars post in
    let markup = lazy text in
    Wg_Tooltip.apply_tooltip_tag buffer ~start ~stop ~markup

  method private is_dummy_id id =
    match id with
    | Edit 0 -> true
    | State id when Stateid.equal id Stateid.dummy -> true
    | _ -> false

  method private enqueue_feedback msg =
    let id = msg.id in
    if self#is_dummy_id id then () else Queue.add msg feedbacks
    
  method private process_feedback () =
    let rec eat_feedback n =
      if n = 0 then true else
      let msg = Queue.pop feedbacks in
      let id = msg.id in
      let sentence =
        let finder s =
          match s.state_id, id with
          | Some id', State id when id = id' -> Some s
          | _, Edit id when id = s.edit_id -> Some s
          | _ -> None in
        try Some (Stack.find_map finder cmd_stack)
        with Not_found -> None in
      let log s sentence =
        Minilib.log ("Feedback " ^ s ^ " on " ^ Stateid.to_string
          (Option.default Stateid.dummy sentence.state_id)) in
      begin match msg.content, sentence with
      | AddedAxiom, Some sentence ->
          log "AddedAxiom" sentence;
          remove_flag sentence `PROCESSING;
          remove_flag sentence `ERROR;
          add_flag sentence `UNSAFE;
          self#mark_as_needed sentence
      | Processed, Some sentence ->
          log "Processed" sentence;
          remove_flag sentence `PROCESSING;
          remove_flag sentence `ERROR;
          self#mark_as_needed sentence
      | GlobRef(loc, filepath, modpath, ident, ty), Some sentence ->
          log "GlobRef" sentence;
          self#attach_tooltip sentence loc
            (Printf.sprintf "%s %s %s" filepath ident ty)
      | ErrorMsg(loc, msg), Some sentence ->
          log "ErrorMsg" sentence;
          remove_flag sentence `PROCESSING;
          add_flag sentence `ERROR;
          self#mark_as_needed sentence;
          self#attach_tooltip sentence loc msg;
          if not (Loc.is_ghost loc) then
            self#position_error_tag_at_sentence sentence (Some (Loc.unloc loc))
      | _ ->
          if sentence <> None then Minilib.log "Unsupported feedback message"
          else if Stack.is_empty cmd_stack then ()
          else
            match id, (Stack.top cmd_stack).state_id with
            | Edit _, _ -> ()
            | State id1, Some id2 when Stateid.newer_than id2 id1 -> ()
            | _ -> Queue.add msg feedbacks (* Put back into the queue *)
      end;
        eat_feedback (n-1)
    in
      eat_feedback (Queue.length feedbacks)

  method private commit_queue_transaction sentence =
    (* A queued command has been successfully done, we push it to [cmd_stack].
       We reget the iters here because Gtk is unable to warranty that they
       were not modified meanwhile. Not really necessary but who knows... *)
    self#mark_as_needed sentence;
    let stop = buffer#get_iter_at_mark sentence.stop in
    buffer#move_mark ~where:stop (`NAME "start_of_input");

  method private position_error_tag_at_iter iter phrase = function
    | None -> ()
    | Some (start, stop) ->
        buffer#apply_tag Tags.Script.error
          ~start:(iter#forward_chars (byte_offset_to_char_offset phrase start))
          ~stop:(iter#forward_chars (byte_offset_to_char_offset phrase stop))

  method private position_error_tag_at_sentence sentence loc =
    let start, _, phrase = self#get_sentence sentence in
    self#position_error_tag_at_iter start phrase loc

  method private process_interp_error queue sentence loc msg id =
    Coq.bind (Coq.return ()) (function () ->
    let start, stop, phrase = self#get_sentence sentence in
    buffer#remove_tag Tags.Script.to_process ~start ~stop;
    self#discard_command_queue queue;
    pop_info ();
    self#position_error_tag_at_iter start phrase loc;
    buffer#place_cursor ~where:start;
    messages#clear;
    messages#push Error msg;
    self#show_goals)

  method private get_sentence sentence =
    let start = buffer#get_iter_at_mark sentence.start in
    let stop = buffer#get_iter_at_mark sentence.stop in
    let phrase = start#get_slice ~stop in
    start, stop, phrase

  (** Compute the phrases until [until] returns [true]. *)
  method private process_until until verbose =
    let push_msg lvl msg = if verbose then messages#push lvl msg in
    let action = Coq.lift (fun () ->
      let queue = Queue.create () in
      (* Lock everything and fill the waiting queue *)
      push_info "Coq is computing";
      messages#clear;
      script#set_editable false;
      self#fill_command_queue until queue;
      (* Now unlock and process asynchronously. Since [until]
        may contain iterators, it shouldn't be used anymore *)
      script#set_editable true;
      Minilib.log "Begin command processing";
      queue)
    in
    Coq.bind action (fun queue ->
    let rec loop () =
      if Queue.is_empty queue then
        let () = pop_info () in
        let () = script#recenter_insert in
        self#show_goals
      else
        let sentence = Queue.pop queue in
        add_flag sentence `PROCESSING;
        Stack.push sentence cmd_stack;
        if List.mem `COMMENT sentence.flags then
          let () = remove_flag sentence `PROCESSING in
          let () = self#commit_queue_transaction sentence in
          loop ()
        else
          (* If the line is not a comment, we interpret it. *)
          let _, _, phrase = self#get_sentence sentence in
          let commit_and_continue msg =
            push_msg Notice msg;
            self#commit_queue_transaction sentence;
            loop ()
          in
          let query =
            Coq.interp ~logger:push_msg ~verbose sentence.edit_id phrase in
          let next = function
          | Good (id, msg) ->
              assign_state_id sentence id;
              commit_and_continue msg
          | Fail (id, loc, msg) ->
              let sentence = Stack.pop cmd_stack in
              self#process_interp_error queue sentence loc msg id
          in
          Coq.bind query next
    in
    loop ())
  
  method join_document =
   let next = function
     | Good _ ->
         messages#clear;
         messages#push Info "Document checked";
         Coq.return ()
     | Fail x -> self#handle_failure x in
   Coq.bind (Coq.status ~logger:messages#push true) next

  method process_next_phrase =
    let until len start stop = 1 <= len in
    let next () =
      buffer#place_cursor ~where:self#get_start_of_input; Coq.return ()
    in
    Coq.bind (self#process_until until true) next

  method private process_until_iter iter =
    let until len start stop =
      if prefs.Preferences.stop_before then stop#compare iter > 0
      else start#compare iter >= 0
    in
    self#process_until until false

  method process_until_end_or_error =
    self#process_until_iter buffer#end_iter

  method private segment_to_be_cleared until =
    let finder (n, found, zone) ({ start; stop; state_id } as sentence) =
      let found = found || until n state_id start stop in
      match found, state_id with
      | true, Some id -> Stop (n, id, Some sentence, zone)
      | _ -> Next (n + 1, found, sentence :: zone) in
    try Stack.seek finder (0, false, []) cmd_stack
    with Not_found ->
      Stack.length cmd_stack, initial_state,
      None, List.rev (Stack.to_list cmd_stack)

  (** Wrapper around the raw undo command *)
  method private backtrack_until ?(move_insert=true) until =
    let opening () =
      push_info "Coq is undoing" in
    let conclusion () =
      pop_info ();
      if move_insert then buffer#place_cursor ~where:self#get_start_of_input;
      self#show_goals in
    let cleanup n l =
      for i = 1 to n do ignore(Stack.pop cmd_stack) done;
      if l <> [] then begin
        let start = buffer#get_iter_at_mark (CList.hd l).start in
        let stop = buffer#get_iter_at_mark (CList.last l).stop in
        buffer#remove_tag Tags.Script.processed ~start ~stop;
        buffer#remove_tag Tags.Script.unjustified ~start ~stop;
(*         buffer#remove_tag Tags.Script.tooltip ~start ~stop; *)
        buffer#remove_tag Tags.Script.to_process ~start ~stop;
        buffer#move_mark ~where:start (`NAME "start_of_input")
      end;
      List.iter (fun { start } -> buffer#delete_mark start) l;
      List.iter (fun { stop } -> buffer#delete_mark stop) l in
    Coq.bind (Coq.lift opening) (fun () ->
    let rec undo until =
      let n, to_id, sentence, seg = self#segment_to_be_cleared until in
      Coq.bind (Coq.backto to_id) (function
      | Good () -> cleanup n seg; conclusion ()
      | Fail (safe_id, loc, msg) ->
          if loc <> None then messages#push Error "Fixme LOC";
          messages#push Error msg;
          undo (fun _ id _ _ -> id = Some safe_id))
    in
      undo until)

  method private backtrack_to_iter ?move_insert iter =
    let until _ _ _ stop = iter#compare (buffer#get_iter_at_mark stop) >= 0 in
    self#backtrack_until ?move_insert until

  method handle_failure (safe_id, (loc : (int * int) option), msg) =
    if loc <> None then messages#push Error "Fixme LOC";
    messages#clear;
    messages#push Error msg;
    ignore(self#process_feedback ());
    let safe_flags s = s.flags = [ `UNSAFE ] || s.flags = [] in
    let find_last_safe_id s =
      match s.state_id with
      | Some id -> safe_flags s | None -> false in
    try
      let last_safe = Stack.find find_last_safe_id cmd_stack in
      self#backtrack_until (fun _ id _ _ -> id = last_safe.state_id)
    with Not_found -> self#backtrack_until (fun _ id _ _ -> id = Some safe_id)

  method backtrack_last_phrase =
    let until n _ _ _ = n >= 1 in
    messages#clear;
    self#backtrack_until until

  method go_to_insert =
    Coq.bind (Coq.return ()) (fun () ->
    messages#clear;
    let point = self#get_insert in
    if point#compare self#get_start_of_input >= 0
    then self#process_until_iter point
    else self#backtrack_to_iter ~move_insert:false point)

  method go_to_mark m =
    Coq.bind (Coq.return ()) (fun () ->
    messages#clear;
    let point = buffer#get_iter_at_mark m in
    if point#compare self#get_start_of_input >= 0
    then self#process_until_iter point
    else self#backtrack_to_iter ~move_insert:false point)


  method tactic_wizard l =
    let insert_phrase phrase tag =
      let stop = self#get_start_of_input in
      let phrase' = if stop#starts_line then phrase else "\n"^phrase in
      buffer#insert ~iter:stop phrase';
      Sentence.tag_on_insert buffer;
      let start = self#get_start_of_input in
      buffer#move_mark ~where:stop (`NAME "start_of_input");
      buffer#apply_tag tag ~start ~stop;
      if self#get_insert#compare stop <= 0 then
        buffer#place_cursor ~where:stop;
      let sentence =
        mk_sentence
          ~start:(`MARK (buffer#create_mark start))
          ~stop:(`MARK (buffer#create_mark stop))
          [] in
      Stack.push sentence cmd_stack;
      messages#clear;
      self#show_goals
    in
    let display_error (loc, s) =
      if not (Glib.Utf8.validate s) then
        flash_info "This error is so nasty that I can't even display it."
      else messages#add s
    in
    let try_phrase phrase stop more =
      let action = log "Sending to coq now" in
      let query = Coq.interp ~verbose:false 0 phrase in
      let next = function
      | Fail (_, l, str) -> (* FIXME: check *)
        display_error (l, str);
        messages#add ("Unsuccessfully tried: "^phrase);
        more
      | Good (_, id) ->
(*         messages#add msg; *)
        stop Tags.Script.processed
      in
      Coq.bind (Coq.seq action query) next
    in
    let rec loop l = match l with
      | [] -> Coq.return ()
      | p :: l' ->
        try_phrase ("progress "^p^".") (insert_phrase (p^".")) (loop l')
    in
    loop l

  method handle_reset_initial why =
    let action () =
      if why = Coq.Unexpected then warning "Coqtop died badly. Resetting.";
      (* clear the stack *)
      while not (Stack.is_empty cmd_stack) do
        let phrase = Stack.pop cmd_stack in
        buffer#delete_mark phrase.start;
        buffer#delete_mark phrase.stop
      done;
      (* reset the buffer *)
      buffer#move_mark ~where:buffer#start_iter (`NAME "start_of_input");
      Sentence.tag_all buffer;
      (* clear the views *)
      messages#clear;
      proof#clear ();
      clear_info ();
      push_info "Restarted";
      (* apply the initial commands to coq *)
    in
    Coq.seq (Coq.lift action) self#initialize

  method initialize =
    let get_initial_state =
      let next = function
      | Fail _ -> messages#set ("Couln't initialize Coq"); Coq.return ()
      | Good id -> initial_state <- id; Coq.return () in
      Coq.bind (Coq.init ()) next in
    let add_load_path = match get_filename () with
    | None -> Coq.return ()
    | Some f ->
      let dir = Filename.dirname f in
      let loadpath = Coq.inloadpath dir in
      let next = function
      | Fail (_, _, s) ->
        messages#set
          ("Could not determine lodpath, this might lead to problems:\n"^s);
        Coq.return ()
      | Good true -> Coq.return ()
      | Good false ->
        let cmd = Printf.sprintf "Add LoadPath \"%s\". "  dir in
        let cmd = Coq.interp (hidden_edit_id ()) cmd in
        let next = function
        | Fail (_, l, str) ->
          messages#set ("Couln't add loadpath:\n"^str);
          Coq.return ()
        | Good (id, _) -> initial_state <- id; Coq.return ()
        in
        Coq.bind cmd next
      in
      Coq.bind loadpath next
    in
    Coq.seq get_initial_state (Coq.seq add_load_path Coq.PrintOpt.enforce)

end
