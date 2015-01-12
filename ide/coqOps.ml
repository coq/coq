(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Coq
open Ideutils
open Interface
open Feedback

type flag = [ `INCOMPLETE | `UNSAFE | `PROCESSING | `ERROR of string ]
type mem_flag = [ `INCOMPLETE | `UNSAFE | `PROCESSING | `ERROR ]
let mem_flag_of_flag : flag -> mem_flag = function
  | `ERROR _ -> `ERROR
  | (`INCOMPLETE | `UNSAFE | `PROCESSING) as mem_flag -> mem_flag
let str_of_flag = function
  | `UNSAFE -> "U"
  | `PROCESSING -> "P"
  | `ERROR _ -> "E"
  | `INCOMPLETE -> "I"

class type signals =
object
  inherit GUtil.ml_signals
  method changed : callback:(int * mem_flag list -> unit) -> GtkSignal.id
end

module SentenceId : sig

  type sentence = private {
    start : GText.mark;
    stop : GText.mark;
    mutable flags : flag list;
    mutable tooltips : (int * int * string) list;
    edit_id : int;
    mutable index : int;
    changed_sig : (int * mem_flag list) GUtil.signal;
  }

  val mk_sentence :
    start:GText.mark -> stop:GText.mark -> flag list -> sentence

  val set_flags : sentence -> flag list -> unit
  val add_flag : sentence -> flag -> unit
  val has_flag : sentence -> mem_flag -> bool
  val remove_flag : sentence -> mem_flag -> unit
  val same_sentence : sentence -> sentence -> bool
  val hidden_edit_id : unit -> int
  val find_all_tooltips : sentence -> int -> string list
  val add_tooltip : sentence -> int -> int -> string -> unit
  val set_index : sentence -> int -> unit

  val connect : sentence -> signals

  val dbg_to_string :
    GText.buffer -> bool -> Stateid.t option -> sentence -> Pp.std_ppcmds

end = struct

  type sentence = {
    start : GText.mark;
    stop : GText.mark;
    mutable flags : flag list;
    mutable tooltips : (int * int * string) list;
    edit_id : int;
    mutable index : int;
    changed_sig : (int * mem_flag list) GUtil.signal;
  }

  let connect s : signals =
    object
      inherit GUtil.ml_signals [s.changed_sig#disconnect]
      method changed = s.changed_sig#connect ~after
    end

  let id = ref 0
  let mk_sentence ~start ~stop flags = decr id; {
    start = start;
    stop = stop;
    flags = flags;
    edit_id = !id;
    tooltips = [];
    index = -1;
    changed_sig = new GUtil.signal ();
  }
  let hidden_edit_id () = decr id; !id

  let changed s =
    s.changed_sig#call (s.index, List.map mem_flag_of_flag s.flags)

  let set_flags s f = s.flags <- f; changed s
  let add_flag s f = s.flags <- CList.add_set (=) f s.flags; changed s
  let has_flag s mf =
    List.exists (fun f -> mem_flag_of_flag f = mf) s.flags
  let remove_flag s mf =
    s.flags <- List.filter (fun f -> mem_flag_of_flag f <> mf) s.flags; changed s
  let same_sentence s1 s2 = s1.edit_id = s2.edit_id
  let find_all_tooltips s off =
    CList.map_filter (fun (start,stop,t) ->
      if start <= off && off <= stop then Some t else None)
    s.tooltips
  let add_tooltip s a b t = s.tooltips <- (a,b,t) :: s.tooltips

  let set_index s i = s.index <- i

  let dbg_to_string (b : GText.buffer) focused id s =
    let ellipsize s =
            Str.global_replace (Str.regexp "^[\n ]*") ""
        (if String.length s > 20 then String.sub s 0 17 ^ "..."
         else s) in
    Pp.str (Printf.sprintf "%s[%3d,%3s](%5d,%5d) %s [%s] %s"
      (if focused then "*" else " ")
      s.edit_id
      (Stateid.to_string (Option.default Stateid.dummy id))
      (b#get_iter_at_mark s.start)#offset
      (b#get_iter_at_mark s.stop)#offset
      (ellipsize
        ((b#get_iter_at_mark s.start)#get_slice (b#get_iter_at_mark s.stop)))
      (String.concat "," (List.map str_of_flag s.flags))
      (ellipsize
        (String.concat ","
          (List.map (fun (a,b,t) ->
             Printf.sprintf "<%d,%d> %s" a b t) s.tooltips))))


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
  method stop_worker : string -> unit task

  method get_n_errors : int
  method get_errors : (int * string) list
  method get_slaves_status : int * int * string CString.Map.t

  method handle_failure : handle_exn_rty -> unit task

  method destroy : unit -> unit
end

let flags_to_color f =
  let of_col c = `NAME (Tags.string_of_color c) in
  if List.mem `PROCESSING f then `NAME "blue"
  else if List.mem `ERROR f then `NAME "red"
  else if List.mem `UNSAFE f then `NAME "orange"
  else if List.mem `INCOMPLETE f then `NAME "gray"
  else of_col (Tags.get_processed_color ())

module Doc = Document

class coqops
  (_script:Wg_ScriptView.script_view)
  (_pv:Wg_ProofView.proof_view)
  (_mv:Wg_MessageView.message_view)
  (_sg:Wg_Segment.segment)
  (_ct:Coq.coqtop)
  get_filename =
object(self)
  val script = _script
  val buffer = (_script#source_buffer :> GText.buffer)
  val proof = _pv
  val messages = _mv
  val segment = _sg

  val document : sentence Doc.document = Doc.create ()
  val mutable document_length = 0

  val mutable initial_state = Stateid.initial

  (* proofs being processed by the slaves *)
  val mutable to_process = 0
  val mutable processed = 0
  val mutable slaves_status = CString.Map.empty

  val feedbacks : feedback Queue.t = Queue.create ()
  val feedback_timer = Ideutils.mktimer ()

  initializer
    Coq.set_feedback_handler _ct self#enqueue_feedback;
    script#misc#set_has_tooltip true;
    ignore(script#misc#connect#query_tooltip ~callback:self#tooltip_callback);
    feedback_timer.Ideutils.run ~ms:300 ~callback:self#process_feedback;
    let on_changed (i, f) = segment#add i (flags_to_color f) in
    let on_push s =
      set_index s document_length;
      (SentenceId.connect s)#changed on_changed;
      document_length <- succ document_length;
      segment#set_length document_length;
      let flags = List.map mem_flag_of_flag s.flags in
      segment#add s.index (flags_to_color flags);
    in
    let on_pop s =
      set_index s (-1);
      document_length <- pred document_length;
      segment#set_length document_length;
    in
    let _ = (Doc.connect document)#pushed on_push in
    let _ = (Doc.connect document)#popped on_pop in
    ()

  method private tooltip_callback ~x ~y ~kbd tooltip =
    let x, y = script#window_to_buffer_coords `WIDGET x y in
    let iter = script#get_iter_at_location x y in
    if iter#has_tag Tags.Script.tooltip then begin
      let s =
        let rec aux iter =
          let marks = iter#marks in
          if marks = [] then aux iter#backward_char
          else
            let mem_marks _ _ s =
              List.exists (fun m ->
                Gobject.get_oid m =
                Gobject.get_oid (buffer#get_mark s.start)) marks in
            try Doc.find document mem_marks 
            with Not_found -> aux iter#backward_char in
        aux iter in
      let ss =
        find_all_tooltips s
          (iter#offset - (buffer#get_iter_at_mark s.start)#offset) in
      let msg = String.concat "\n" (CList.uniquize ss) in
      GtkBase.Tooltip.set_icon_from_stock tooltip `INFO `BUTTON;
      script#misc#set_tooltip_markup ("<tt>" ^ msg ^ "</tt>")
    end else begin
      script#misc#set_tooltip_text ""; script#misc#set_has_tooltip true
    end;
    false
    
  method destroy () =
    feedback_timer.Ideutils.kill ()

  method private print_stack =
    Minilib.log "document:";
    Minilib.log (Pp.string_of_ppcmds (Doc.print document (dbg_to_string buffer)))

  method private enter_focus start stop =
    let at id id' _ = Stateid.equal id' id in
    self#print_stack;
    Minilib.log("Focusing "^Stateid.to_string start^" "^Stateid.to_string stop);
    Doc.focus document ~cond_top:(at start) ~cond_bot:(at stop);
    self#print_stack;
    let qed_s = Doc.tip_data document in
    buffer#apply_tag Tags.Script.read_only
      ~start:((buffer#get_iter_at_mark qed_s.start)#forward_find_char
        (fun c -> not(Glib.Unichar.isspace c)))
      ~stop:(buffer#get_iter_at_mark qed_s.stop);
    buffer#move_mark ~where:(buffer#get_iter_at_mark qed_s.stop)
      (`NAME "stop_of_input")

  method private exit_focus =
    Minilib.log "Unfocusing";
    begin try
      let { start; stop } = Doc.tip_data document in
      buffer#remove_tag Tags.Script.read_only
        ~start:(buffer#get_iter_at_mark start)
        ~stop:(buffer#get_iter_at_mark stop)
    with Doc.Empty -> () end;
    Doc.unfocus document;
    self#print_stack;
    begin try
      let where = buffer#get_iter_at_mark (Doc.tip_data document).stop in
      buffer#move_mark ~where (`NAME "start_of_input");
    with Doc.Empty -> () end;
    buffer#move_mark ~where:buffer#end_iter (`NAME "stop_of_input")

  method private get_start_of_input =
    buffer#get_iter_at_mark (`NAME "start_of_input")
  
  method private get_end_of_input =
    buffer#get_iter_at_mark (`NAME "stop_of_input")

  method private get_insert =
    buffer#get_iter_at_mark `INSERT

  method private show_goals_aux ?(move_insert=false) () =
    Coq.PrintOpt.set_printing_width proof#width;
    if move_insert then begin
      buffer#place_cursor ~where:self#get_start_of_input;
      script#recenter_insert;
    end;
    Coq.bind (Coq.goals ~logger:messages#push ()) (function
    | Fail x -> self#handle_failure_aux ~move_insert x
    | Good goals ->
      Coq.bind (Coq.evars ()) (function
        | Fail x -> self#handle_failure_aux ~move_insert x
        | Good evs ->
          proof#set_goals goals;
          proof#set_evars evs;
          proof#refresh ();
          Coq.return ()
        )
      )
  method show_goals = self#show_goals_aux ()

  (* This method is intended to perform stateless commands *)
  method raw_coq_query phrase =
    let action = log "raw_coq_query starting now" in
    let display_error s =
      if not (Glib.Utf8.validate s) then
        flash_info "This error is so nasty that I can't even display it."
      else messages#add s;
    in
    let query =
      Coq.query ~logger:messages#push (phrase,Stateid.dummy) in
    let next = function
    | Fail (_, _, err) -> display_error err; Coq.return ()
    | Good msg ->
      messages#add msg; Coq.return ()
    in
    Coq.bind (Coq.seq action query) next

  method private mark_as_needed sentence =
    Minilib.log("Marking " ^
      Pp.string_of_ppcmds (dbg_to_string buffer false None sentence));
    let start = buffer#get_iter_at_mark sentence.start in
    let stop = buffer#get_iter_at_mark sentence.stop in
    let to_process = Tags.Script.to_process in
    let processed = Tags.Script.processed in
    let unjustified = Tags.Script.unjustified in
    let error_bg = Tags.Script.error_bg in
    let error = Tags.Script.error in
    let incomplete = Tags.Script.incomplete in
    let all_tags = [
      error_bg; to_process; incomplete; processed; unjustified; error ] in
    let tags =
      (if has_flag sentence `PROCESSING then [to_process]
       else if has_flag sentence `ERROR then [error_bg]
       else if has_flag sentence `INCOMPLETE then [incomplete]
       else [processed]) @
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
    let markup = Glib.Markup.escape_text text in
    buffer#apply_tag Tags.Script.tooltip ~start ~stop;
    add_tooltip sentence pre post markup

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
        let finder _ state_id s =
          match state_id, id with
          | Some id', State id when Stateid.equal id id' -> Some (state_id, s)
          | _, Edit id when id = s.edit_id -> Some (state_id, s)
          | _ -> None in
        try Some (Doc.find_map document finder)
        with Not_found -> None in
      let log s state_id =
        Minilib.log ("Feedback " ^ s ^ " on " ^ Stateid.to_string
          (Option.default Stateid.dummy state_id)) in
      begin match msg.contents, sentence with
      | AddedAxiom, Some (id,sentence) ->
          log "AddedAxiom" id;
          remove_flag sentence `PROCESSING;
          remove_flag sentence `ERROR;
          add_flag sentence `UNSAFE;
          self#mark_as_needed sentence
      | Processed, Some (id,sentence) ->
          log "Processed" id;
          remove_flag sentence `PROCESSING;
          remove_flag sentence `ERROR;
          self#mark_as_needed sentence
      | ProcessingIn _,  Some (id,sentence) ->
          log "ProcessingIn" id;
          add_flag sentence `PROCESSING;
          self#mark_as_needed sentence
      | Incomplete, Some (id, sentence) ->
          log "Incomplete" id;
          add_flag sentence `INCOMPLETE;
          self#mark_as_needed sentence
      | Complete, Some (id, sentence) ->
          log "Complete" id;
          remove_flag sentence `INCOMPLETE;
          self#mark_as_needed sentence
      | GlobRef(loc, filepath, modpath, ident, ty), Some (id,sentence) ->
          log "GlobRef" id;
          self#attach_tooltip sentence loc
            (Printf.sprintf "%s %s %s" filepath ident ty)
      | ErrorMsg(loc, msg), Some (id,sentence) ->
          log "ErrorMsg" id;
          remove_flag sentence `PROCESSING;
          add_flag sentence (`ERROR msg);
          self#mark_as_needed sentence;
          self#attach_tooltip sentence loc msg;
          if not (Loc.is_ghost loc) then
            self#position_error_tag_at_sentence sentence (Some (Loc.unloc loc))
      | InProgress n, _ ->
          if n < 0 then processed <- processed + abs n
          else to_process <- to_process + n
      | WorkerStatus(id,status), _ ->
          log "WorkerStatus" None;
          slaves_status <- CString.Map.add id status slaves_status

      | _ ->
          if sentence <> None then Minilib.log "Unsupported feedback message"
          else if Doc.is_empty document then ()
          else
            try
              match id, Doc.tip document with
              | Edit _, _ -> ()
              | State id1, id2 when Stateid.newer_than id2 id1 -> ()
              | _ -> Queue.add msg feedbacks
            with Doc.Empty | Invalid_argument _ -> Queue.add msg feedbacks 
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

  method private process_interp_error queue sentence loc msg tip id =
    Coq.bind (Coq.return ()) (function () ->
    let start, stop, phrase = self#get_sentence sentence in
    buffer#remove_tag Tags.Script.to_process ~start ~stop;
    self#discard_command_queue queue;
    pop_info ();
    if Stateid.equal id tip || Stateid.equal id Stateid.dummy then begin
      self#position_error_tag_at_iter start phrase loc;
      buffer#place_cursor ~where:stop;
      messages#clear;
      messages#push Pp.Error msg;
      self#show_goals
    end else
      self#show_goals_aux ~move_insert:true ()
    )

  method private get_sentence sentence =
    let start = buffer#get_iter_at_mark sentence.start in
    let stop = buffer#get_iter_at_mark sentence.stop in
    let phrase = start#get_slice ~stop in
    start, stop, phrase

  (** [fill_command_queue until q] fills a command queue until the [until]
      condition returns true; it is fed with the number of phrases read and the
      iters enclosing the current sentence. *)
  method private fill_command_queue until queue =
    let rec loop n iter =
      match Sentence.find buffer iter with
      | None -> ()
      | Some (start, stop) ->
        if until n start stop then begin
          ()
        end else if start#has_tag Tags.Script.processed then begin
          Queue.push (`Skip (start, stop)) queue;
          loop n stop
        end else begin
          buffer#apply_tag Tags.Script.to_process ~start ~stop;
          let sentence =
            mk_sentence
              ~start:(`MARK (buffer#create_mark start))
              ~stop:(`MARK (buffer#create_mark stop))
              [] in
          Queue.push (`Sentence sentence) queue;
          if not stop#is_end then loop (succ n) stop
        end
    in
    loop 0 self#get_start_of_input

  method private discard_command_queue queue =
    while not (Queue.is_empty queue) do
      match Queue.pop queue with
      | `Skip _ -> ()
      | `Sentence sentence ->
          let start = buffer#get_iter_at_mark sentence.start in
          let stop = buffer#get_iter_at_mark sentence.stop in
          buffer#remove_tag Tags.Script.to_process ~start ~stop;
          buffer#delete_mark sentence.start;
          buffer#delete_mark sentence.stop;
    done

  (** Compute the phrases until [until] returns [true]. *)
  method private process_until ?move_insert until verbose =
    let logger lvl msg = if verbose then messages#push lvl msg in
    let fill_queue = Coq.lift (fun () ->
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
      queue) in
    let conclude topstack =
      pop_info ();
      script#recenter_insert;
      match topstack with
      | [] -> self#show_goals_aux ?move_insert ()
      | (_,s) :: _ -> self#backtrack_to_iter (buffer#get_iter_at_mark s.start) in
    let process_queue queue =
      let rec loop tip topstack =
        if Queue.is_empty queue then conclude topstack else
        match Queue.pop queue, topstack with
        | `Skip(start,stop), [] -> assert false
        | `Skip(start,stop), (_,s) :: topstack ->
            assert(start#equal (buffer#get_iter_at_mark s.start));
            assert(stop#equal (buffer#get_iter_at_mark s.stop));
            loop tip topstack
        | `Sentence sentence, _ :: _ -> assert false
        | `Sentence ({ edit_id } as sentence), [] ->
            add_flag sentence `PROCESSING;
            Doc.push document sentence;
            let _, _, phrase = self#get_sentence sentence in
            let coq_query = Coq.add ~logger ((phrase,edit_id),(tip,verbose)) in
            let handle_answer = function
              | Good (id, (Util.Inl (* NewTip *) (), msg)) ->
                  Doc.assign_tip_id document id;
                  logger Pp.Notice msg;
                  self#commit_queue_transaction sentence;
                  loop id []
              | Good (id, (Util.Inr (* Unfocus *) tip, msg)) ->
                  Doc.assign_tip_id document id;
                  let topstack, _ = Doc.context document in
                  self#exit_focus;
                  self#cleanup (Doc.cut_at document tip);
                  logger Pp.Notice msg;
                  self#mark_as_needed sentence;
                  if Queue.is_empty queue then loop tip []
                  else loop tip (List.rev topstack)
              | Fail (id, loc, msg) ->
                  let sentence = Doc.pop document in
                  self#process_interp_error queue sentence loc msg tip id in
            Coq.bind coq_query handle_answer
      in
      let tip =
        try Doc.tip document
        with Doc.Empty -> initial_state | Invalid_argument _ -> assert false in
      loop tip [] in
    Coq.bind fill_queue process_queue
  
  method join_document =
   let next = function
     | Good _ ->
         messages#clear;
         messages#push Pp.Info "All proof terms checked by the kernel";
         Coq.return ()
     | Fail x -> self#handle_failure x in
   Coq.bind (Coq.status ~logger:messages#push true) next

  method stop_worker n =
    Coq.bind (Coq.stop_worker n) (fun _ -> Coq.return ())

  method get_slaves_status = processed, to_process, slaves_status

  method get_n_errors =
    Doc.fold_all document 0 (fun n _ _ s -> if has_flag s `ERROR then n+1 else n)

  method get_errors =
    let extract_error s =
      match List.find (function `ERROR _ -> true | _ -> false) s.flags with
      | `ERROR msg -> (buffer#get_iter_at_mark s.start)#line + 1, msg
      | _ -> assert false in
    List.rev
      (Doc.fold_all document [] (fun acc _ _ s ->
        if has_flag s `ERROR then extract_error s :: acc else acc))

  method process_next_phrase =
    let until n _ _ = n >= 1 in
    self#process_until ~move_insert:true until true

  method private process_until_iter iter =
    let until _ start stop =
      if prefs.Preferences.stop_before then stop#compare iter > 0
      else start#compare iter >= 0
    in
    self#process_until until false

  method process_until_end_or_error =
    self#process_until_iter self#get_end_of_input

  (* finds the state_id and if it an unfocus is needed to reach it *)
  method private find_id until =
    try
      Doc.find_id document (fun id { start;stop } -> until (Some id) start stop)
    with Not_found -> initial_state, Doc.focused document 

  method private cleanup seg =
    if seg <> [] then begin
      let start = buffer#get_iter_at_mark (CList.last seg).start in
      let stop = buffer#get_iter_at_mark (CList.hd seg).stop in
      Minilib.log
        (Printf.sprintf "Cleanup in range %d -> %d" start#offset stop#offset);
      buffer#remove_tag Tags.Script.processed ~start ~stop;
      buffer#remove_tag Tags.Script.incomplete ~start ~stop;
      buffer#remove_tag Tags.Script.unjustified ~start ~stop;
      buffer#remove_tag Tags.Script.tooltip ~start ~stop;
      buffer#remove_tag Tags.Script.to_process ~start ~stop;
      buffer#move_mark ~where:start (`NAME "start_of_input")
    end;
    List.iter (fun { start } -> buffer#delete_mark start) seg;
    List.iter (fun { stop } -> buffer#delete_mark stop) seg

  (** Wrapper around the raw undo command *)
  method private backtrack_to_id ?(move_insert=true) (to_id, unfocus_needed) =
    Minilib.log("backtrack_to_id "^Stateid.to_string to_id^
      " (unfocus_needed="^string_of_bool unfocus_needed^")");
    let opening () =
      push_info "Coq is undoing" in
    let conclusion () =
      pop_info ();
      if move_insert then buffer#place_cursor ~where:self#get_start_of_input;
      let start = self#get_start_of_input in
      let stop = self#get_end_of_input in
      Minilib.log(Printf.sprintf "cleanup tags %d %d" start#offset stop#offset);
      buffer#remove_tag Tags.Script.tooltip ~start ~stop;
      buffer#remove_tag Tags.Script.processed ~start ~stop;
      buffer#remove_tag Tags.Script.incomplete ~start ~stop;
      buffer#remove_tag Tags.Script.to_process ~start ~stop;
      buffer#remove_tag Tags.Script.unjustified ~start ~stop;
      self#show_goals in
    Coq.bind (Coq.lift opening) (fun () ->
    let rec undo to_id unfocus_needed =
      Coq.bind (Coq.edit_at to_id) (function
      | Good (CSig.Inl (* NewTip *) ()) ->
          if unfocus_needed then self#exit_focus;
          self#cleanup (Doc.cut_at document to_id);
          conclusion ()
      | Good (CSig.Inr (* Focus  *) (stop_id,(start_id,tip))) ->
          if unfocus_needed then self#exit_focus;
          self#cleanup (Doc.cut_at document tip);
          self#enter_focus start_id stop_id;
          self#cleanup (Doc.cut_at document to_id);
          conclusion ()
      | Fail (safe_id, loc, msg) ->
          if loc <> None then messages#push Pp.Error "Fixme LOC";
          messages#push Pp.Error msg;
          if Stateid.equal safe_id Stateid.dummy then self#show_goals
          else undo safe_id
                 (Doc.focused document && Doc.is_in_focus document safe_id))
    in
      undo to_id unfocus_needed)
  
  method private backtrack_until ?move_insert until =
    self#backtrack_to_id ?move_insert (self#find_id until)

  method private backtrack_to_iter ?move_insert iter =
    let until _ _ stop = iter#compare (buffer#get_iter_at_mark stop) >= 0 in
    self#backtrack_until ?move_insert until

  method private handle_failure_aux
    ?(move_insert=false) (safe_id, (loc : (int * int) option), msg)
  =
    messages#clear;
    messages#push Pp.Error msg;
    ignore(self#process_feedback ());
    if Stateid.equal safe_id Stateid.dummy then Coq.lift (fun () -> ())
    else
      Coq.seq
        (self#backtrack_until ~move_insert
          (fun id _ _ -> id = Some safe_id))
        (Coq.lift (fun () -> script#recenter_insert))

  method handle_failure f = self#handle_failure_aux f

  method backtrack_last_phrase =
    messages#clear;
    try 
      let tgt = Doc.before_tip document in
      self#backtrack_to_id tgt
    with Not_found -> Coq.return (Coq.reset_coqtop _ct)

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
    then Coq.seq (self#process_until_iter point)
          (Coq.lift (fun () -> Sentence.tag_on_insert buffer))
    else Coq.seq (self#backtrack_to_iter ~move_insert:false point)
          (Coq.lift (fun () -> Sentence.tag_on_insert buffer)))

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
      Doc.push document sentence;
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
      let query = Coq.query (phrase,Stateid.dummy) in
      let next = function
      | Fail (_, l, str) -> (* FIXME: check *)
        display_error (l, str);
        messages#add ("Unsuccessfully tried: "^phrase);
        more
      | Good msg ->
        messages#add msg;
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
      if why = Coq.Unexpected then warning "Coqtop died badly. Resetting."
      else
      (* clear the stack *)
      if Doc.focused document then Doc.unfocus document;
      while not (Doc.is_empty document) do
        let phrase = Doc.pop document in
        buffer#delete_mark phrase.start;
        buffer#delete_mark phrase.stop
      done;
      List.iter
        (buffer#remove_tag ~start:buffer#start_iter ~stop:buffer#end_iter)
        Tags.Script.all;
      (* reset the buffer *)
      buffer#move_mark ~where:buffer#start_iter (`NAME "start_of_input");
      buffer#move_mark ~where:buffer#end_iter (`NAME "stop_of_input");
      Sentence.tag_all buffer;
      (* clear the views *)
      messages#clear;
      proof#clear ();
      clear_info ();
      processed <- 0;
      to_process <- 0;
      push_info "Restarted";
      (* apply the initial commands to coq *)
    in
    Coq.seq (Coq.lift action) self#initialize

  method initialize =
    let get_initial_state =
      let next = function
      | Fail _ -> messages#set ("Couln't initialize Coq"); Coq.return ()
      | Good id -> initial_state <- id; Coq.return () in
      Coq.bind (Coq.init (get_filename ())) next in
    Coq.seq get_initial_state Coq.PrintOpt.enforce

end
