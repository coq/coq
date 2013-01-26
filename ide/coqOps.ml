(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Coq
open Ideutils

type flag = [ `COMMENT | `UNSAFE ]

type ide_info = {
  start : GText.mark;
  stop : GText.mark;
  flags : flag list;
}

let prefs = Preferences.current

let log msg : unit task =
  Coq.lift (fun () -> Minilib.log msg)

class type ops =
object
  method go_to_insert : unit task
  method tactic_wizard : string list -> unit task
  method process_next_phrase : unit task
  method process_until_end_or_error : unit task
  method handle_reset_initial : Coq.reset_kind -> unit task
  method raw_coq_query : string -> unit task
  method show_goals : unit task
  method backtrack_last_phrase : unit task
  method initialize : unit task
end

class coqops
  (_script:Wg_ScriptView.script_view)
  (_pv:Wg_ProofView.proof_view)
  (_mv:Wg_MessageView.message_view)
  get_filename =
object(self)
  val script = _script
  val buffer = (_script#source_buffer :> GText.buffer)
  val proof = _pv
  val messages = _mv

  val cmd_stack = Stack.create ()

  method private get_start_of_input =
    buffer#get_iter_at_mark (`NAME "start_of_input")

  method private get_insert =
    buffer#get_iter_at_mark `INSERT

  method show_goals =
    Coq.PrintOpt.set_printing_width proof#width;
    Coq.bind Coq.goals (function
    | Interface.Fail (l, str) ->
      messages#set ("Error in coqtop:\n"^str);
      Coq.return ()
    | Interface.Good goals | Interface.Unsafe goals ->
      Coq.bind Coq.evars (function
        | Interface.Fail (l, str)->
          messages#set ("Error in coqtop:\n"^str);
          Coq.return ()
        | Interface.Good evs | Interface.Unsafe evs ->
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
    let query = Coq.interp ~logger:messages#push ~raw:true ~verbose:false phrase in
    let next = function
    | Interface.Fail (_, err) -> display_error err; Coq.return ()
    | Interface.Good msg | Interface.Unsafe msg ->
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
        let payload = {
          start = `MARK (buffer#create_mark start);
          stop = `MARK (buffer#create_mark stop);
          flags = if is_comment then [`COMMENT] else [];
        } in
        Queue.push payload queue;
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

  method private commit_queue_transaction queue sentence newflags =
    (* A queued command has been successfully done, we push it to [cmd_stack].
       We reget the iters here because Gtk is unable to warranty that they
       were not modified meanwhile. Not really necessary but who knows... *)
    let start = buffer#get_iter_at_mark sentence.start in
    let stop = buffer#get_iter_at_mark sentence.stop in
    let sentence = { sentence with flags = newflags @ sentence.flags } in
    let tag =
      if List.mem `UNSAFE newflags then Tags.Script.unjustified
      else Tags.Script.processed
    in
    buffer#move_mark ~where:stop (`NAME "start_of_input");
    buffer#apply_tag tag ~start ~stop;
    buffer#remove_tag Tags.Script.to_process ~start ~stop;
    ignore (Queue.pop queue);
    Stack.push sentence cmd_stack

  method private process_error queue phrase loc msg =
    Coq.bind (Coq.return ()) (function () ->
    let position_error = function
      | None -> ()
      | Some (start, stop) ->
        let soi = self#get_start_of_input in
        let start =
          soi#forward_chars (byte_offset_to_char_offset phrase start) in
        let stop =
          soi#forward_chars (byte_offset_to_char_offset phrase stop) in
        buffer#apply_tag Tags.Script.error ~start ~stop;
        buffer#place_cursor ~where:start
    in
    self#discard_command_queue queue;
    pop_info ();
    position_error loc;
    messages#clear;
    messages#push Interface.Error msg;
    self#show_goals)

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
        let sentence = Queue.peek queue in
        if List.mem `COMMENT sentence.flags then
          (self#commit_queue_transaction queue sentence []; loop ())
        else
          (* If the line is not a comment, we interpret it. *)
          let phrase =
            let start = buffer#get_iter_at_mark sentence.start in
            let stop = buffer#get_iter_at_mark sentence.stop in
            start#get_slice ~stop
          in
          let commit_and_continue msg flags =
            push_msg Interface.Notice msg;
            self#commit_queue_transaction queue sentence flags;
            loop ()
          in
          let query = Coq.interp ~logger:push_msg ~verbose phrase in
          let next = function
          | Interface.Good msg -> commit_and_continue msg []
          | Interface.Unsafe msg -> commit_and_continue msg [`UNSAFE]
          | Interface.Fail (loc, msg) ->
            self#process_error queue phrase loc msg
          in
          Coq.bind query next
    in
    loop ())

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

  (** Clear the command stack until [until] returns [true].
      Returns the number of commands sent to Coqtop to backtrack. *)
  method private prepare_clear_zone until zone =
    let merge_zone phrase zone =
      match zone with
        | None -> Some (phrase.start, phrase.stop)
        | Some (start,stop) ->
          (* phrase should be just before the current clear zone *)
          buffer#delete_mark phrase.stop;
          buffer#delete_mark start;
          Some (phrase.start, stop)
    in
    let rec loop len real_len zone =
      if Stack.is_empty cmd_stack then real_len, zone
      else
        let phrase = Stack.top cmd_stack in
        let is_comment = List.mem `COMMENT phrase.flags in
        if until len real_len phrase.start phrase.stop then
          real_len, zone
        else
          (* [until] has not been reached, so we'll clear this command *)
          let _ = Stack.pop cmd_stack in
          let zone = merge_zone phrase zone in
          loop (succ len) (if is_comment then real_len else succ real_len) zone
    in
    loop 0 0 zone

  method private commit_clear_zone = function
    | None -> ()
    | Some (start_mark, stop_mark) ->
      let start = buffer#get_iter_at_mark start_mark in
      let stop = buffer#get_iter_at_mark stop_mark in
      buffer#remove_tag Tags.Script.processed ~start ~stop;
      buffer#remove_tag Tags.Script.unjustified ~start ~stop;
      buffer#move_mark ~where:start (`NAME "start_of_input");
      buffer#delete_mark start_mark;
      buffer#delete_mark stop_mark

  (** Actually performs the undoing *)
  method private undo_command_stack n clear_zone =
    let next = function
    | Interface.Good n | Interface.Unsafe n ->
      let until _ len _ _ = n <= len in
      (* Coqtop requested [n] more ACTUAL backtrack *)
      let _, zone = self#prepare_clear_zone until clear_zone in
      self#commit_clear_zone zone;
      Coq.return ()
    | Interface.Fail (l, str) ->
      messages#set
        ("Error while backtracking: " ^ str ^
          "\nCoqIDE and coqtop may be out of sync," ^
          "you may want to use Restart.");
      Coq.return ()
    in
    Coq.bind (Coq.rewind n) next

  (** Wrapper around the raw undo command *)
  method private backtrack_until until =
    let action () = 
      push_info "Coq is undoing";
      messages#clear
    in
    Coq.bind (Coq.lift action) (fun () ->
    (* Instead of locking the whole buffer, we now simply remove
       read-only tags *after* the actual backtrack *)
      let to_undo, zone = self#prepare_clear_zone until None in
      let next () = pop_info (); Coq.return () in
      Coq.bind (self#undo_command_stack to_undo zone) next
    )

  method private backtrack_to_iter iter =
    let until _ _ _ stop =
      iter#compare (buffer#get_iter_at_mark stop) >= 0
    in
    Coq.seq (self#backtrack_until until)
      (* We may have backtracked too much: let's replay *)
      (self#process_until_iter iter)

  method backtrack_last_phrase =
    let until len _ _ _ = 1 <= len in
    Coq.bind (self#backtrack_until until)
      (fun () ->
        buffer#place_cursor ~where:self#get_start_of_input;
        self#show_goals)

  method go_to_insert =
    Coq.bind (Coq.return ()) (fun () ->
    let point = self#get_insert in
    if point#compare self#get_start_of_input >= 0
    then self#process_until_iter point
    else self#backtrack_to_iter point)

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
      let ide_payload = {
        start = `MARK (buffer#create_mark start);
        stop = `MARK (buffer#create_mark stop);
        flags = [];
      } in
      Stack.push ide_payload cmd_stack;
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
      let query = Coq.interp ~verbose:false phrase in
      let next = function
      | Interface.Fail (l, str) ->
        display_error (l, str);
        messages#add ("Unsuccessfully tried: "^phrase);
        more
      | Interface.Good msg ->
        messages#add msg;
        stop Tags.Script.processed
      | Interface.Unsafe msg ->
        messages#add msg;
        stop Tags.Script.unjustified
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

  method private include_file_dir_in_path =
    let query f =
      let dir = Filename.dirname f in
      let loadpath = Coq.inloadpath dir in
      let next = function
      | Interface.Fail (_, s) ->
        messages#set
          ("Could not determine lodpath, this might lead to problems:\n"^s);
        Coq.return ()
      | Interface.Good true | Interface.Unsafe true -> Coq.return ()
      | Interface.Good false | Interface.Unsafe false ->
        let cmd = Printf.sprintf "Add LoadPath \"%s\". "  dir in
        let cmd = Coq.interp cmd in
        let next = function
        | Interface.Fail (l, str) ->
          messages#set ("Couln't add loadpath:\n"^str);
          Coq.return ()
        | Interface.Good _ | Interface.Unsafe _ ->
          Coq.return ()
        in
        Coq.bind cmd next
      in
      Coq.bind loadpath next
    in
    let next () = match get_filename () with
    | None -> Coq.return ()
    | Some f -> query f
    in
    Coq.bind (Coq.return ()) next

  method initialize =
    let next () = Coq.PrintOpt.enforce in
    Coq.bind self#include_file_dir_in_path next

end
