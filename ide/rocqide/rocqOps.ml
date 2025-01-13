(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open RocqDriver
open Interface
open Feedback

type flag = [ `INCOMPLETE | `UNSAFE | `PROCESSING | `ERROR of string Loc.located | `WARNING of string Loc.located ]
type mem_flag = [ `INCOMPLETE | `UNSAFE | `PROCESSING | `ERROR | `WARNING ]
let mem_flag_of_flag : flag -> mem_flag = function
  | `ERROR _ -> `ERROR
  | `WARNING _ -> `WARNING
  | (`INCOMPLETE | `UNSAFE | `PROCESSING) as mem_flag -> mem_flag
let str_of_flag = function
  | `UNSAFE -> "U"
  | `PROCESSING -> "P"
  | `ERROR _ -> "E"
  | `WARNING _ -> "W"
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
    start_offset : int;
    (** Original start offset of the sentence, to be compared when moved *)
    start_line : int;
    (** Original start line of the sentence, to be compared when moved *)
    edit_id : int;
    mutable index : int;
    changed_sig : (int * mem_flag list) GUtil.signal;
  }

  val mk_sentence :
    start:GText.mark -> stop:GText.mark -> start_offset:int -> start_line:int -> flag list -> sentence

  val add_flag : sentence -> flag -> unit
  val has_flag : sentence -> mem_flag -> bool
  val remove_flag : sentence -> mem_flag -> unit
  val find_all_tooltips : sentence -> int -> string list
  val add_tooltip : sentence -> int -> int -> string -> unit
  val set_index : sentence -> int -> unit

  val connect : sentence -> signals

  val start_iter : GText.buffer -> sentence -> GText.iter
  val start_stop_iters : GText.buffer -> sentence -> GText.iter * GText.iter

  (** [offset_compensation] Drift of a sentence over its original
      location, as an [(offset, line)] pair. Needed to repair outdated
      Rocq locations *)
  val offset_compensation : GText.buffer -> sentence -> int * int

  val phrase : GText.buffer -> sentence -> string

  val dbg_to_string :
    GText.buffer -> bool -> Stateid.t option -> sentence -> Pp.t

end = struct

  type sentence = {
    start : GText.mark;
    stop : GText.mark;
    mutable flags : flag list;
    mutable tooltips : (int * int * string) list;
    start_offset : int;
    (** Original start offset of the sentence, to be compared when moved *)
    start_line : int;
    (** Original start line of the sentence, to be compared when moved *)
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
  let mk_sentence ~start ~stop ~start_offset ~start_line flags = decr id; {
    start;
    stop;
    flags;
    edit_id = !id;
    tooltips = [];
    start_offset;
    start_line;
    index = -1;
    changed_sig = new GUtil.signal ();
  }

  let changed s =
    s.changed_sig#call (s.index, List.map mem_flag_of_flag s.flags)

  let add_flag s f = s.flags <- CList.add_set (=) f s.flags; changed s
  let has_flag s mf =
    List.exists (fun f -> mem_flag_of_flag f = mf) s.flags
  let remove_flag s mf =
    s.flags <- List.filter (fun f -> mem_flag_of_flag f <> mf) s.flags; changed s
  let find_all_tooltips s off =
    CList.map_filter (fun (start,stop,t) ->
      if start <= off && off <= stop then Some t else None)
    s.tooltips
  let add_tooltip s a b t = s.tooltips <- (a,b,t) :: s.tooltips

  let set_index s i = s.index <- i

  let start_iter buffer sentence = buffer#get_iter_at_mark sentence.start
  let stop_iter buffer sentence = buffer#get_iter_at_mark sentence.stop
  let start_stop_iters buffer sentence = start_iter buffer sentence, stop_iter buffer sentence
  let offset_compensation buffer sentence =
    let s_start = buffer#get_iter_at_mark sentence.start in
    s_start#offset - sentence.start_offset, s_start#line - sentence.start_line

  let phrase buffer sentence =
    let start, stop = start_stop_iters buffer sentence in
    start#get_slice ~stop

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
        ((b#get_iter_at_mark s.start)#get_slice ~stop:(b#get_iter_at_mark s.stop)))
      (String.concat "," (List.map str_of_flag s.flags))
      (ellipsize
        (String.concat ","
          (List.map (fun (a,b,t) ->
             Printf.sprintf "<%d,%d> %s" a b t) s.tooltips))))


end
open SentenceId

(* Given a Rocq loc, convert it to a pair of iterators start / end in
   the buffer. *)
let rocq_loc_to_gtk_offset ?(line_drift=0) (buffer : GText.buffer) loc =
  Ideutils.get_iter_at_byte buffer ~line:(loc.Loc.line_nb - 1 + line_drift) (loc.bp - loc.bol_pos),
  Ideutils.get_iter_at_byte buffer ~line:(loc.Loc.line_nb_last - 1 + line_drift) (loc.ep - loc.bol_pos_last)

(** increase [uni_off] by the number of bytes until [s_uni] This can
    be used to convert a character offset to byte offset if we know a
    previous point denoted by the pair [s_byte, s_uni] *)
let c2b (buffer : GText.buffer) (s_byte, s_uni) uni_off =
  if s_uni < 0 then
    raise (invalid_arg "c2b: s_uni must be >= 0");
  let rec cvt iter rv =
    if iter#offset <= s_uni then
      rv
    else
      cvt iter#backward_char (rv + (Ideutils.ulen iter#char))
  in
  cvt (buffer#get_iter (`OFFSET uni_off)) s_byte

(* Given [sentence], returns [bp, line, bol] where [bp] is the
   absolute offset in _bytes_ for the start of [sentence], [line] is
   the line number for the start of sentence and [bol] is the line
   ofsset of [sentence] in _bytes_.

   This is meant to be used in the resumption of parsing, to tell Rocq
   where the input stream was left at. In this case, these 3 points
   uniquely determine the position where to restart
   from. [CLexer.after] can compute this from the position of the last
   parsed token.

   However, for RocqIDE, we have a huge problem in the sense that
   RocqIDE will do its own parsing and the locations may not start at
   the same point. Thus, we need to perform potentially very costly
   char to offset conversion, for that we need the whole buffer.
*)
let rocq_loc_from_gtk_offset cached buffer sentence =
  let start = start_iter buffer sentence in
  (* This is in chars not in bytes, thus needs conversion *)
  let bp = c2b buffer cached start#offset in
  (* Rocq lines start at 1, GTK lines at 0 *)
  let line = start#line + 1 in
  (* [line_index] already returns byte offsets *)
  let bol_pos = bp - start#line_index in
  (*  *)
  let new_cached = bp, start#offset in
  bp, line, bol_pos, new_cached

let log msg : unit task =
  RocqDriver.lift (fun () -> Minilib.log msg)

class type ops =
object
  method go_to_insert : unit task
  method go_to_mark : GText.mark -> unit task
  method process_next_phrase : unit task
  method process_db_cmd : string ->
    next:(Interface.db_cmd_rty Interface.value -> unit task) -> unit task
  method process_db_configd : unit ->
    next:(Interface.db_configd_rty Interface.value -> unit task) -> unit task
  method process_db_upd_bpts : ((string * int) * bool) list ->
    next:(Interface.db_upd_bpts_rty Interface.value -> unit task) -> unit task
  method process_db_continue : db_continue_opt ->
    next:(Interface.db_continue_rty Interface.value -> unit task) -> unit task
  method process_db_stack :
    next:(Interface.db_stack_rty Interface.value -> unit task) -> unit task
  method process_db_vars : int ->
    next:(Interface.db_vars_rty Interface.value -> unit task) -> unit task
  method process_until_end_or_error : unit task
  method handle_reset_initial : unit task
  method raw_rocq_query :
    route_id:int -> next:(query_rty value -> unit task) -> string -> unit task
  method proof_diff : GText.mark -> next:(Pp.t value -> unit task) -> unit task
  method show_goals : unit task
  method backtrack_last_phrase : unit task
  method initialize : unit task
  method join_document : unit task
  method stop_worker : string -> unit task

  method get_n_errors : int
  method get_warnings : (int * string) list
  method get_errors : (int * string) list
  method get_slaves_status : int * int * string CString.Map.t
  method backtrack_to_begin : unit -> unit task
  method handle_failure : handle_exn_rty -> unit task

  method destroy : unit -> unit
  method scroll_to_start_of_input : unit -> unit
  method set_forward_clear_db_highlight : (unit -> unit) -> unit
  method set_forward_set_goals_of_dbg_session : (Pp.t -> unit) -> unit
  method set_forward_init_db : (unit -> unit) -> unit
  method set_debug_goal : Pp.t -> unit
end

let flags_to_color f =
  if List.mem `PROCESSING f then `NAME "blue"
  else if List.mem `ERROR f then `NAME "red"
  else if List.mem `UNSAFE f then `NAME "orange"
  else if List.mem `INCOMPLETE f then `NAME "gray"
  else `NAME Preferences.processed_color#get

module Doc = Document

let segment_model (doc : sentence Doc.document) : Wg_Segment.model =
object (self)

  val mutable cbs = []

  val mutable document_length = 0

  method length = document_length

  method changed ~callback = cbs <- callback :: cbs

  method fold : 'a. ('a -> Wg_Segment.color -> 'a) -> 'a -> 'a = fun f accu ->
    let fold accu _ _ s =
      let flags = List.map mem_flag_of_flag s.flags in
      f accu (flags_to_color flags)
    in
    Doc.fold_all doc accu fold

  method private on_changed (i, f) =
    let data = (i, flags_to_color f) in
    List.iter (fun f -> f (`SET data)) cbs

  method private on_push s ctx =
    let after = match ctx with
    | None -> []
    | Some (l, _) -> l
    in
    List.iter (fun s -> set_index s (s.index + 1)) after;
    set_index s (document_length - List.length after);
    ignore ((SentenceId.connect s)#changed ~callback:self#on_changed);
    document_length <- document_length + 1;
    List.iter (fun f -> f `INSERT) cbs

  method private on_pop s ctx =
    let () = match ctx with
    | None -> ()
    | Some (l, _) -> List.iter (fun s -> set_index s (s.index - 1)) l
    in
    set_index s (-1);
    document_length <- document_length - 1;
    List.iter (fun f -> f `REMOVE) cbs

  initializer
    let _ = (Doc.connect doc)#pushed ~callback:self#on_push in
    let _ = (Doc.connect doc)#popped ~callback:self#on_pop in
    ()

end

type queue_msg =
  | MsgFeedback of Feedback.feedback
  | MsgDebug of string * Pp.t

let rec flatten = function
| [] -> []
| (lg, rg) :: l ->
  let inner = flatten l in
  List.rev_append lg inner @ rg

class rocqops
  (_script:Wg_ScriptView.script_view)
  (_pv:Wg_ProofView.proof_view)
  (_mv:Wg_RoutedMessageViews.message_views_router)
  (_sg:Wg_Segment.segment)
  (_ct:RocqDriver.rocqtop)
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

  val mutable last_offsets = (0,0)

  val mutable forward_clear_db_highlight = ((fun x -> failwith "forward_clear_db_highlight")
                  : unit -> unit)

  val mutable forward_set_goals_of_dbg_session = ((fun x -> failwith "forward_set_goals_of_dbg_session")
                  : Pp.t -> unit)

  val mutable forward_init_db = ((fun x -> failwith "forward_init_db")
                  : unit -> unit)
  initializer
    RocqDriver.set_feedback_handler _ct
        (fun msg -> self#process_feedback (MsgFeedback msg));
    RocqDriver.set_debug_prompt_handler _ct
        (fun ~tag msg -> self#process_feedback (MsgDebug (tag, msg)));
    script#misc#set_has_tooltip true;
    ignore(script#misc#connect#query_tooltip ~callback:self#tooltip_callback);
    let md = segment_model document in
    segment#set_model md;
    let on_click id =
      let find _ _ s = Int.equal s.index id in
      let sentence = Doc.find document find in
      let mark = sentence.start in
      let iter = script#buffer#get_iter_at_mark mark in
      (* Sentence starts tend to be at the end of a line, so we rather choose
         the first non-line-ending position. *)
      let rec sentence_start iter =
        if iter#ends_line then sentence_start iter#forward_line
        else iter
      in
      let iter = sentence_start iter in
      script#buffer#place_cursor ~where:iter;
      ignore (script#scroll_to_iter ~use_align:true ~yalign:0. iter)
    in
    let _ = segment#connect#clicked ~callback:on_click in
    ()

  method private tooltip_callback ~x ~y ~kbd tooltip =
    let x, y = script#window_to_buffer_coords ~tag:`WIDGET ~x ~y in
    let iter = script#get_iter_at_location ~x ~y in
    if iter#has_tag Tags.Script.tooltip then begin
      let s : SentenceId.sentence =
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
      (* The original list of tooltips contains offset that were not
         set up to date if the sentences moved, however the GTK model
         has the up-to-date information in the marks, so we can
         compare and compensate for the shift. *)
      let offset, _line_shift = offset_compensation script#buffer s in
      let ss = find_all_tooltips s (iter#offset - offset) in
      let ss = if ss = [] then Doc.get_errors document else ss in
      let msg = CString.html_escape (String.concat "\n" (CList.uniquize ss)) in
      GtkBase.Tooltip.set_icon_from_stock tooltip `INFO `BUTTON;
      script#misc#set_tooltip_markup ("<tt>" ^ msg ^ "</tt>")
    end else begin
      script#misc#set_tooltip_text ""; script#misc#set_has_tooltip true
    end;
    false

  method destroy () = ()

  method scroll_to_start_of_input () =
    let start = buffer#get_iter_at_mark (`NAME "start_of_input") in
    ignore (script#scroll_to_iter ~use_align:true ~yalign:0. start)

  method set_forward_clear_db_highlight f =
    forward_clear_db_highlight <- f

  method set_forward_set_goals_of_dbg_session f =
    forward_set_goals_of_dbg_session <- f

  method set_forward_init_db f =
    forward_init_db <- f

  method private print_stack =
    Minilib.log "document:";
    Minilib.log_pp (Doc.print document (dbg_to_string buffer))

  method private enter_focus start stop =
    let at id id' _ = Stateid.equal id' id in
    self#print_stack;
    Minilib.log("Focusing "^Stateid.to_string start^" "^Stateid.to_string stop);
    Doc.focus document ~cond_top:(at start) ~cond_bot:(at stop);
    self#print_stack;
    let qed_s = Doc.tip_data document in
    buffer#move_mark ~where:(buffer#get_iter_at_mark qed_s.stop)
      (`NAME "stop_of_input")

  method private exit_focus =
    Minilib.log "Unfocusing";
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
    if move_insert then begin
      let dest = self#get_start_of_input in
      if (buffer#get_iter_at_mark `INSERT)#compare dest <= 0 then begin
        buffer#place_cursor ~where:dest;
        script#recenter_insert
      end
    end;
    let flags = { gf_mode = "full"; gf_fg = true; gf_bg = true; gf_shelved = false; gf_given_up = false } in
    let return x = RocqDriver.return (Good x) in
    let (>>=) m f = RocqDriver.bind m (function
    | Fail x -> RocqDriver.return (Fail x)
    | Good v -> f v)
    in
    let call =
      RocqDriver.subgoals flags >>= begin function
      | None -> return Wg_ProofView.NoGoals
      | Some { fg_goals = ((_ :: _) as fg); bg_goals = bg } ->
        let bg = flatten (List.rev bg) in
        return (Wg_ProofView.FocusGoals { fg; bg; })
      | Some { fg_goals = []; bg_goals = bg } ->
        let flags = { gf_mode = "short"; gf_fg = false; gf_bg = false; gf_shelved = true; gf_given_up = true } in
        RocqDriver.subgoals flags >>= fun rem ->
        let bg = flatten (List.rev bg) in
        let shelved, given_up = match rem with
        | None -> [], []
        | Some goals -> goals.shelved_goals, goals.given_up_goals
        in
        return (Wg_ProofView.NoFocusGoals { bg; shelved; given_up })
      end
    in
    RocqDriver.bind call begin function
    | Fail x -> self#handle_failure_aux ~move_insert x
    | Good goals ->
      proof#set_goals goals;
      proof#refresh ~force:true;
      RocqDriver.return ()
    end

  method show_goals = self#show_goals_aux ()

  (* This method is intended to perform stateless commands *)
  method raw_rocq_query ~route_id ~next phrase : unit RocqDriver.task =
    let sid = try Document.tip document
              with Document.Empty -> Stateid.initial
    in
    let action = log "raw_rocq_query starting now" in
    let query = RocqDriver.query (route_id,(phrase,sid)) in
    RocqDriver.bind (RocqDriver.seq action query) next

  method proof_diff where ~next : unit RocqDriver.task =
    (* todo: would be nice to ignore comments, too *)
    let rec back iter =
      if iter#is_start then iter
      else
        let c = iter#char in
        if Glib.Unichar.isspace c || c = 0 then back (iter#backward_char)
        else if c = int_of_char '.' then iter#backward_char
        else iter in

    let where = back (buffer#get_iter_at_mark where) in
    let until _ start stop =
      (buffer#get_iter_at_mark stop)#compare where >= 0 &&
      (buffer#get_iter_at_mark start)#compare where <= 0 in
    let state_id = fst @@ self#find_id until in
      let diff_opt = Interface.(match RocqDriver.PrintOpt.(get diff) with
        | StringValue diffs -> diffs
        | _ -> "off") in
      let proof_diff = RocqDriver.proof_diff (diff_opt, state_id) in
      RocqDriver.bind proof_diff next

  method private still_valid { edit_id = id } =
    try ignore(Doc.find_id document (fun _ { edit_id = id1 } -> id = id1)); true
    with Not_found -> false

  method private mark_as_needed sentence =
   if self#still_valid sentence then begin
    Minilib.log_pp Pp.(str "Marking " ++ dbg_to_string buffer false None sentence);
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
      (if has_flag sentence `UNSAFE then [unjustified] else [])
    in
    List.iter (fun t -> buffer#remove_tag t ~start ~stop) all_tags;
    List.iter (fun t -> buffer#apply_tag t ~start ~stop) tags
   end

  (* Invariant, we store the tooltips with "original" Rocq locations,
     that means we must correct the offset even the Some case will get
     the actual offset, beware this is a big fragile, but kinda
     inherent to the model *)
  method private attach_tooltip ?loc sentence text =
    let offset, line_drift = offset_compensation buffer sentence in
    let start, stop = match loc with
      | None ->
        start_stop_iters buffer sentence
      | Some loc ->
        rocq_loc_to_gtk_offset ~line_drift buffer loc
    in
    let markup = Glib.Markup.escape_text text in
    buffer#apply_tag Tags.Script.tooltip ~start ~stop;
    add_tooltip sentence (start#offset - offset) (stop#offset - offset) markup

  method private debug_prompt ~tag msg =
    match tag with
    | "prompt" ->
      messages#default_route#debug_prompt msg
    | "goal" ->
      forward_set_goals_of_dbg_session msg
    | "init" -> forward_init_db ()
    | _ ->
      messages#default_route#push Debug msg

  method set_debug_goal msg =
    proof#set_debug_goal msg

  method private process_feedback msg =
    (* Minilib.log ("Feedback received: " ^ Xml_printer.to_string_fmt Xmlprotocol.(of_feedback Ppcmds msg)); *)
    let pr_feedback msg =
      let id = msg.span_id in
      let sentence =
        let finder _ state_id s =
          match state_id, id with
          | Some id', id when Stateid.equal id id' -> Some (state_id, s)
          | _ -> None in
        try Some (Doc.find_map document finder)
        with Not_found -> None in
      let log_pp ?id s =
        Minilib.log_pp Pp.(seq
                [str "Feedback "; s; pr_opt (fun id -> str " on " ++ str (Stateid.to_string id)) id])
      in
      let msg_wo_sent mtype =
        Minilib.log (mtype ^ " feedback message without a sentence") in
      let unsupp_msg mtype =
        if sentence <> None then
          Minilib.log ("Unsupported feedback message " ^ mtype ^ " with a sentence")
      in
      let log ?id s = log_pp ?id (Pp.str s) in
      begin match msg.contents, sentence with
      | AddedAxiom, Some (id,sentence) ->
          log ?id "AddedAxiom";
          remove_flag sentence `PROCESSING;
          remove_flag sentence `ERROR;
          add_flag sentence `UNSAFE;
          self#mark_as_needed sentence
      | AddedAxiom, None ->  msg_wo_sent "AddedAxiom"
      | Processed, Some (id,sentence) ->
          log ?id "Processed" ;
          remove_flag sentence `PROCESSING;
          self#mark_as_needed sentence;
          forward_clear_db_highlight ()
      | Processed, None ->  msg_wo_sent "Processed"
      | ProcessingIn _,  Some (id,sentence) ->
          log ?id "ProcessingIn";
          add_flag sentence `PROCESSING;
          self#mark_as_needed sentence
      | ProcessingIn _, None ->  msg_wo_sent "ProcessingIn"
      | Incomplete, Some (id, sentence) ->
          log ?id "Incomplete";
          add_flag sentence `INCOMPLETE;
          self#mark_as_needed sentence
      | Incomplete, None ->  msg_wo_sent "Incomplete"
      | Complete, Some (id, sentence) ->
          log ?id "Complete";
          remove_flag sentence `INCOMPLETE;
          self#mark_as_needed sentence
      | Complete, None ->  msg_wo_sent "Complete"
      | GlobRef(loc, filepath, modpath, ident, ty), Some (id,sentence) ->
          log ?id "GlobRef";
          self#attach_tooltip ~loc sentence
            (Printf.sprintf "%s %s %s" filepath ident ty)
      | GlobRef (_, _, _, _, _), None -> msg_wo_sent "GlobRef"
      | Message(Error, loc, _, msg), Some (id,sentence) ->
          log_pp ?id Pp.(str "ErrorMsg " ++ msg);
          remove_flag sentence `PROCESSING;
          let rmsg = Pp.string_of_ppcmds msg in
          add_flag sentence (`ERROR (loc, rmsg));
          self#mark_as_needed sentence;
          self#attach_tooltip ?loc sentence rmsg;
          self#apply_tag_in_sentence ?loc Tags.Script.error sentence
      | Message(Warning, loc, _, message), Some (id,sentence) ->
          log_pp ?id Pp.(str "WarningMsg " ++ message);
          let rmsg = Pp.string_of_ppcmds message in
          add_flag sentence (`WARNING (loc, rmsg));
          self#attach_tooltip ?loc sentence rmsg;
          self#apply_tag_in_sentence ?loc Tags.Script.warning sentence;
          (messages#route msg.route)#push Warning message
      | Message(lvl, loc, _, message), Some (id,sentence) ->
          log_pp ?id Pp.(str "Msg " ++ message);
          (messages#route msg.route)#push lvl message
      (* We do nothing here as for BZ#5583 *)
      | Message(Error, loc, _, msg), None ->
          log_pp Pp.(str "Error Msg without a sentence" ++ msg)
      | Message(lvl, loc, _, message), None ->
          log_pp Pp.(str "Msg without a sentence " ++ message);
          (messages#route msg.route)#push lvl message
      | InProgress n, _ ->
          if n < 0 then processed <- processed + abs n
          else to_process <- to_process + n
      | WorkerStatus(id,status), _ ->
          log "WorkerStatus";
          slaves_status <- CString.Map.add id status slaves_status
      (* log unused feedback messages with a sentence *)
      | GlobDef (_, _, _, _), _ -> unsupp_msg "GlobDef"
      | FileDependency (_, _), _ -> unsupp_msg "FileDependency"
      | FileLoaded (_, _), _ -> unsupp_msg "FileLoaded"
      | Custom (_, _, _), _  -> unsupp_msg "Custom"
      end
    in
    try match msg with
      | MsgFeedback msg2 -> pr_feedback msg2
      | MsgDebug (tag, msg2) ->
        if tag = "prompt" then
          RocqDriver.set_stopped_in_debugger _ct true;
        self#debug_prompt ~tag msg2
    with e -> (Printf.printf "Exception: %s\n%!" (Printexc.to_string e);
        flush stdout;
        raise e)

  method private commit_queue_transaction sentence =
    (* A queued command has been successfully done, we push it to [cmd_stack].
       We reget the iters here because Gtk is unable to warranty that they
       were not modified meanwhile. Not really necessary but who knows... *)
    self#mark_as_needed sentence;
    let stop = buffer#get_iter_at_mark sentence.stop in
    buffer#move_mark ~where:stop (`NAME "start_of_input");

  method private apply_tag_in_sentence ?loc tag sentence =
    match loc with
    | None ->
      let start, stop = start_stop_iters buffer sentence in
      buffer#apply_tag tag ~start ~stop
    | Some loc ->
      let _offset, line_drift = offset_compensation buffer sentence in
      let start, stop = rocq_loc_to_gtk_offset ~line_drift buffer loc in
      buffer#apply_tag tag ~start ~stop

  method private process_interp_error ?loc queue sentence msg tip id =
    RocqDriver.bind (RocqDriver.return ()) (function () ->
    let start, stop = start_stop_iters buffer sentence in
    buffer#remove_tag Tags.Script.to_process ~start ~stop;
    self#discard_command_queue queue;
    Ideutils.pop_info ();
    if Stateid.equal id tip || Stateid.equal id Stateid.dummy then begin
      self#attach_tooltip ?loc sentence (Pp.string_of_ppcmds msg);
      self#apply_tag_in_sentence ?loc Tags.Script.error sentence;
      buffer#place_cursor ~where:stop;
      messages#default_route#clear;
      messages#default_route#push Feedback.Error msg;
      self#show_goals
    end else
      self#show_goals_aux ~move_insert:true ()
    )

  (** [fill_command_queue until q] fills a command queue until the [until]
      condition returns true; it is fed with the number of phrases read and the
      iters enclosing the current sentence. *)
  method private fill_command_queue until queue =
    let topstack =
      if Doc.focused document then fst (Doc.context document) else [] in
    let rec loop n iter prev_start =
      (* prev_start is a workaround to avoid an endless loop.  See #15873/#15984 *)
      match Sentence.find buffer iter with
      | None -> ()
      | Some (start, stop) ->
        if until n start stop then begin
          ()
        end else if
          List.exists (fun (_, s) ->
            start#equal (buffer#get_iter_at_mark s.start) &&
            stop#equal (buffer#get_iter_at_mark s.stop)) topstack
        then begin
          Queue.push (`Skip (start, stop)) queue;
          loop n stop start#offset
        end else begin
          buffer#apply_tag Tags.Script.to_process ~start ~stop;
          let sentence =
            let start_offset = start#offset in
            let start_line = start#line in
            let start = `MARK (buffer#create_mark start) in
            let stop = `MARK (buffer#create_mark stop) in
            mk_sentence ~start ~stop ~start_offset ~start_line []
          in
          Queue.push (`Sentence sentence) queue;
          if start#offset <> prev_start && not stop#is_end then loop (succ n) stop start#offset
        end
    in
    loop 0 self#get_start_of_input (-1)

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
    let logger lvl msg = if verbose then messages#default_route#push lvl msg in
    let fill_queue = RocqDriver.lift (fun () ->
      let queue = Queue.create () in
      (* Lock everything and fill the waiting queue *)
      Ideutils.push_info "Coq is computing";
      messages#default_route#clear;
      script#set_editable false;
      self#fill_command_queue until queue;
      (* Now unlock and process asynchronously. Since [until]
        may contain iterators, it shouldn't be used anymore *)
      script#set_editable true;
      Minilib.log "Begin command processing";
      queue) in
    let conclude topstack =
      Ideutils.pop_info ();
      script#recenter_insert;
      match topstack with
      | [] -> self#show_goals_aux ?move_insert ()
      | (_,s)::_ -> self#backtrack_to_iter (buffer#get_iter_at_mark s.start) in
    let process_queue queue =
      let rec loop tip topstack =
        if Queue.is_empty queue then conclude topstack else
        match Queue.pop queue, topstack with
        | `Skip(start,stop), [] ->
            logger Feedback.Error (Pp.str "You must close the proof with Qed or Admitted");
            self#discard_command_queue queue;
            conclude []
        | `Skip(start,stop), (_,s) :: topstack ->
            assert(start#equal (buffer#get_iter_at_mark s.start));
            assert(stop#equal (buffer#get_iter_at_mark s.stop));
            loop tip topstack
        | `Sentence sentence, _ :: _ -> assert false
        | `Sentence ({ edit_id } as sentence), [] ->
            add_flag sentence `PROCESSING;
            Doc.push document sentence;
            let phrase = phrase buffer sentence in
            (* When we retract, the cached offsets are invalid, thus we need to reset the cache *)
            let start = start_iter buffer sentence in
            let cached_offset = if start#offset > (snd last_offsets) then last_offsets else (0,0) in
            let bp, line_nb, bol_pos, new_cached = rocq_loc_from_gtk_offset cached_offset buffer sentence in
            last_offsets <- new_cached;
            let rocq_query = RocqDriver.add ((((phrase,edit_id),(tip,verbose)),bp),(line_nb,bol_pos)) in
            Doc.set_errors document [];
            let handle_answer = function
              | Good (id, Util.Inl (* NewTip *) ()) ->
                  Doc.assign_tip_id document id;
                  self#commit_queue_transaction sentence;
                  loop id []
              | Good (id, Util.Inr (* Unfocus *) tip) ->
                  Doc.assign_tip_id document id;
                  let topstack, _ = Doc.context document in
                  self#exit_focus;
                  self#cleanup (Doc.cut_at document tip);
                  self#mark_as_needed sentence;
                  if Queue.is_empty queue then loop tip []
                  else loop tip (List.rev topstack)
              | Fail (id, loc, msg) ->
                  let sentence = Doc.pop document in
                  Doc.set_errors document [Pp.string_of_ppcmds msg];
                  self#process_interp_error ?loc queue sentence msg tip id in
            RocqDriver.bind rocq_query handle_answer
      in
      let tip =
        try Doc.tip document
        with Doc.Empty -> initial_state | Invalid_argument _ -> assert false in
      loop tip [] in
    RocqDriver.bind fill_queue process_queue

  method join_document =
   let next = function
     | Good _ ->
         messages#default_route#clear;
         messages#default_route#push
           Feedback.Info (Pp.str "All proof terms checked by the kernel");
         RocqDriver.return ()
     | Fail x -> self#handle_failure x in
   RocqDriver.bind (RocqDriver.status true) next

  method stop_worker n =
    RocqDriver.bind (RocqDriver.stop_worker n) (fun _ -> RocqDriver.return ())

  method get_slaves_status = processed, to_process, slaves_status

  method get_n_errors =
    Doc.fold_all document 0 (fun n _ _ s -> if has_flag s `ERROR then n+1 else n)

  method private get_flagged (f : flag -> (Loc.t option * string) option) =
    let extract s =
      let map item = match f item with
      | None -> None
      | Some (loc, msg) ->
        let iter = match loc with
        | None -> buffer#get_iter_at_mark s.start
        | Some loc -> fst (rocq_loc_to_gtk_offset buffer loc)
        in
        Some (iter#line + 1, msg)
      in
      List.map_filter map s.flags
    in
    List.rev (Doc.fold_all document [] (fun acc _ _ s -> extract s @ acc))

  method get_warnings =
    let f (item : flag) = match item with
    | `WARNING (loc, msg) -> Some (loc, msg)
    | _ -> None
    in
    self#get_flagged f

  method get_errors =
    let f (item : flag) = match item with
    | `ERROR (loc, msg) -> Some (loc, msg)
    | _ -> None
    in
    self#get_flagged f

  method process_next_phrase =
    let until n _ _ = n >= 1 in
    self#process_until ~move_insert:true until true

  method process_db_cmd cmd ~next : unit RocqDriver.task =
    let db_cmd = RocqDriver.db_cmd cmd in
    RocqDriver.bind db_cmd next

  method process_db_configd cmd ~next : unit RocqDriver.task =
    let db_configd = RocqDriver.db_configd cmd in
    RocqDriver.bind db_configd next

  method process_db_upd_bpts updates ~next : unit RocqDriver.task =
    let db_upd_bpts = RocqDriver.db_upd_bpts updates in
    RocqDriver.bind db_upd_bpts next

  method process_db_continue opt ~next : unit RocqDriver.task =
    let db_continue = RocqDriver.db_continue opt in
    RocqDriver.bind db_continue next

  method process_db_stack ~next : unit RocqDriver.task =
    let db_stack = RocqDriver.db_stack () in
    RocqDriver.bind db_stack next

  method process_db_vars framenum ~next : unit RocqDriver.task =
    let db_vars = RocqDriver.db_vars framenum in
    RocqDriver.bind db_vars next

  method private process_until_iter iter =
    let until _ start stop =
      if Preferences.stop_before#get then stop#compare iter > 0
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
    List.iter (fun { stop } -> buffer#delete_mark stop) seg;
    self#print_stack

  (** Wrapper around the raw undo command *)
  method private backtrack_to_id ?(move_insert=true) (to_id, unfocus_needed) =
    Minilib.log("backtrack_to_id "^Stateid.to_string to_id^
      " (unfocus_needed="^string_of_bool unfocus_needed^")");
    let opening () =
      Ideutils.push_info "Coq is undoing" in
    let conclusion () =
      Ideutils.pop_info ();
      if move_insert then begin
        buffer#place_cursor ~where:self#get_start_of_input;
        script#recenter_insert;
      end;
      let start = self#get_start_of_input in
      let stop = self#get_end_of_input in
      Minilib.log(Printf.sprintf "cleanup tags %d %d" start#offset stop#offset);
      buffer#remove_tag Tags.Script.tooltip ~start ~stop;
      buffer#remove_tag Tags.Script.processed ~start ~stop;
      buffer#remove_tag Tags.Script.incomplete ~start ~stop;
      buffer#remove_tag Tags.Script.to_process ~start ~stop;
      buffer#remove_tag Tags.Script.unjustified ~start ~stop;
      self#show_goals in
    RocqDriver.bind (RocqDriver.lift opening) (fun () ->
    let rec undo to_id unfocus_needed =
      RocqDriver.bind (RocqDriver.edit_at to_id) (function
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
(*           if loc <> None then messages#push Feedback.Error (Richpp.richpp_of_string "Fixme LOC"); *)
          messages#default_route#push Feedback.Error msg;
          if Stateid.equal safe_id Stateid.dummy then self#show_goals
          else undo safe_id
                 (Doc.focused document && Doc.is_in_focus document safe_id))
    in
      undo to_id unfocus_needed)

  method backtrack_to_begin =
    let until (id : Doc.id option) _ stop = (id = (Some (Stateid.of_int 1))) in
    fun () -> self#backtrack_to_id ~move_insert:false (self#find_id until)

  method private backtrack_until ?move_insert until =
    self#backtrack_to_id ?move_insert (self#find_id until)

  method private backtrack_to_iter ?move_insert iter =
    let until _ _ stop = iter#compare (buffer#get_iter_at_mark stop) >= 0 in
    self#backtrack_until ?move_insert until

  method private handle_failure_aux
    ?(move_insert=false) (safe_id, (loc : Interface.location), msg)
  =
    messages#default_route#push Feedback.Error msg;
    if Stateid.equal safe_id Stateid.dummy then RocqDriver.lift (fun () -> ())
    else
      RocqDriver.seq
        (self#backtrack_until ~move_insert
          (fun id _ _ -> id = Some safe_id))
        (RocqDriver.lift (fun () -> script#recenter_insert))

  method handle_failure f = self#handle_failure_aux f

  method backtrack_last_phrase =
    messages#default_route#clear;
    try
      let tgt = Doc.before_tip document in
      self#backtrack_to_id tgt
    with Not_found -> RocqDriver.return (RocqDriver.reset_rocqtop _ct)

  method go_to_insert =
    RocqDriver.bind (RocqDriver.return ()) (fun () ->
    messages#default_route#clear;
    let point = self#get_insert in
    if point#compare self#get_start_of_input >= 0
    then self#process_until_iter point
    else self#backtrack_to_iter ~move_insert:false point)

  method go_to_mark m =
    RocqDriver.bind (RocqDriver.return ()) (fun () ->
    messages#default_route#clear;
    let point = buffer#get_iter_at_mark m in
    if point#compare self#get_start_of_input >= 0
    then RocqDriver.seq (self#process_until_iter point)
          (RocqDriver.lift (fun () -> Sentence.tag_on_insert buffer))
    else RocqDriver.seq (self#backtrack_to_iter ~move_insert:false point)
          (RocqDriver.lift (fun () -> Sentence.tag_on_insert buffer)))

  method handle_reset_initial =
    let action () =
      (* clear the stack *)
      if Doc.focused document then Doc.unfocus document;
      while not (Doc.is_empty document) do
        let phrase = Doc.pop document in
        buffer#delete_mark phrase.start;
        buffer#delete_mark phrase.stop
      done;
      List.iter
        (buffer#remove_tag ~start:buffer#start_iter ~stop:buffer#end_iter)
        Tags.Script.all_but_bpt;
      (* reset the buffer *)
      buffer#move_mark ~where:buffer#start_iter (`NAME "start_of_input");
      buffer#move_mark ~where:buffer#end_iter (`NAME "stop_of_input");
      Sentence.tag_all buffer;
      (* clear the views *)
      messages#default_route#clear;
      proof#clear ();
      Ideutils.clear_info ();
      processed <- 0;
      to_process <- 0;
      Ideutils.push_info "Restarted";
      (* apply the initial commands to rocq *)
    in
    RocqDriver.seq (RocqDriver.lift action) self#initialize

  method initialize =
    let get_initial_state =
      let next = function
      | Fail (_, _, message) ->
        let message = "Couldn't initialize coqtop\n\n" ^ (Pp.string_of_ppcmds message) in
        let popup = GWindow.message_dialog ~buttons:GWindow.Buttons.ok ~message_type:`ERROR ~message () in
        ignore (popup#run ()); exit 1
      | Good id -> initial_state <- id; RocqDriver.return () in
      RocqDriver.bind (RocqDriver.init (get_filename ())) next in
    RocqDriver.seq get_initial_state RocqDriver.PrintOpt.enforce

end
