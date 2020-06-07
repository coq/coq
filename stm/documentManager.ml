(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Scheduler

type position =
  { line : int;
    char : int;
  }

let compare_position pos1 pos2 =
  match Int.compare pos1.line pos2.line with
  | 0 -> Int.compare pos1.char pos2.char
  | x -> x

let position_to_string pos = Format.sprintf "(%i,%i)" pos.line pos.char

type range =
  { range_start : position;
    range_end : position;
  }

let log msg = Format.eprintf "@[%s@]@\n%!" msg

type text_edit = range * string

type proof_data = (Proof.data * position) option

let top_edit_position edits =
  match edits with
  | [] -> assert false
  | ({ range_start },_) :: edits ->
    List.fold_left (fun min ({ range_start },_) ->
    if compare_position range_start min < 0 then range_start else min) range_start edits

let bottom_edit_position edits =
  match edits with
  | [] -> assert false
  | ({ range_end },_) :: edits ->
    List.fold_left (fun max ({ range_end },_) ->
    if compare_position range_end max > 0 then range_end else max) range_end edits

module LM = Map.Make (Int)

type sentence_id = Stateid.t

module SM = Map.Make (Stateid)

type parsed_ast =
  | ValidAst of ast * Tok.t list
  | ParseError of string Loc.located

let string_of_parsed_ast = function
  | ValidAst (ast,tokens) -> (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^ " [" ^ String.concat "--" (List.map (Tok.extract_string false) tokens) ^ "]"
  | ParseError _ -> "(parse error)"

type pre_sentence = {
  start : int;
  stop : int;
  parsing_state : Vernacstate.Parser.state; (* st used to parse this sentence *)
  ast : parsed_ast;
}

type sentence = {
  start : int;
  stop : int;
  parsing_state : Vernacstate.Parser.state; (* st used to parse this sentence *)
  scheduler_state_before : Scheduler.state;
  scheduler_state_after : Scheduler.state;
  ast : parsed_ast;
  id : sentence_id;
}

let string_of_sentence sentence =
  Format.sprintf "[%s] %s (%i -> %i)" (Stateid.to_string sentence.id)
  (string_of_parsed_ast sentence.ast)
  sentence.start
  sentence.stop

let same_tokens (s1 : sentence) (s2 : pre_sentence) =
  match s1.ast, s2.ast with
  | ValidAst (_,tokens1), ValidAst (_,tokens2) ->
    CList.equal Tok.equal tokens1 tokens2
  | _ -> false

module RawDoc : sig

  type t

  val create : string -> t
  val text : t -> string

  val position_of_loc : t -> int -> position
  val loc_of_position : t -> position -> int
  val end_loc : t -> int

  val range_of_loc : t -> Loc.t -> range

  type edit = range * string

  val apply_text_edit : t -> edit -> t * int

end = struct

  type t = {
    text : string;
    lines : int array; (* locs of beginning of lines *)
  }

  let compute_lines text =
    let lines = String.split_on_char '\n' text in
    let _,lines_locs = CList.fold_left_map (fun acc s -> let n = String.length s in n + acc + 1, acc) 0 lines in
    Array.of_list lines_locs

  let create text = { text; lines = compute_lines text }

  let text t = t.text

  let position_of_loc raw loc =
    let i = ref 0 in
    while (!i < Array.length raw.lines && raw.lines.(!i) <= loc) do incr(i) done;
    { line = !i - 1; char = loc - raw.lines.(!i - 1) }

  let loc_of_position raw { line; char } =
    raw.lines.(line) + char

  let end_loc raw =
    String.length raw.text

  let range_of_loc raw loc =
    { range_start = position_of_loc raw loc.Loc.bp;
      range_end = position_of_loc raw loc.Loc.ep;
    }

  type edit = range * string

  let apply_text_edit raw ({range_start; range_end}, editText) =
    let range_start = loc_of_position raw range_start in
    let range_end = loc_of_position raw range_end in
    let before = String.sub raw.text 0 range_start in
    let after = String.sub raw.text range_end (String.length raw.text - range_end) in
    let new_text = before ^ editText ^ after in (* FIXME avoid concatenation *)
    let new_lines = compute_lines new_text in (* FIXME compute this incrementally *)
    let old_length = range_end - range_start in
    let shift = String.length editText - old_length in
    { text = new_text; lines = new_lines }, shift

end

type severity =
  | Warning
  | Error

type diagnostic = {
  range : range;
  message : string;
  severity : severity;
}

type vernac_classification =
  ParsingEffect | StateEffect

let classify_vernac ast =
  let open Vernacextend in
  match Vernac_classifier.classify_vernac ast with
  | VtSideff (_, VtNow) -> ParsingEffect
  | _ -> StateEffect

let classify_parsed_vernac = function
  | ValidAst (ast,_tokens) -> classify_vernac ast
  | ParseError _ -> StateEffect (* Optimistic error recovery *)

module ParsedDoc : sig

  type t

  val empty : t

  val to_string : t -> string

  val schedule : t -> schedule

  val parsed_ranges : RawDoc.t -> t -> range list
  val executed_ranges : RawDoc.t -> t -> ExecutionManager.state -> int -> range list

  val make_diagnostic : RawDoc.t -> t -> sentence_id -> Loc.t option -> string -> severity -> diagnostic
  val parse_errors : RawDoc.t -> t -> diagnostic list

  val add_sentence : t -> int -> int -> parsed_ast -> Vernacstate.Parser.state -> Scheduler.state -> t * Scheduler.state
  val remove_sentence : t -> sentence_id -> t
  val remove_sentences_after : t -> int -> t * Stateid.Set.t
  val sentences_before : t -> int -> sentence list
  val sentences_after : t -> int -> sentence list
  val find_sentence : t -> int -> sentence option
  val find_sentence_before : t -> int -> sentence option
  val shift_sentences : t -> int -> int -> t

  val previous_sentence : t -> sentence_id -> sentence option
  val next_sentence : t -> sentence_id -> sentence option

  val pos_at_end : t -> int
  val state_at_end : t -> ExecutionManager.state -> (int * Vernacstate.Parser.state * Scheduler.state) option
  val state_at_pos : t -> ExecutionManager.state -> int -> (int * Vernacstate.Parser.state * Scheduler.state) option

  val patch_sentence : t -> Scheduler.state -> sentence_id -> pre_sentence -> t * Scheduler.state

  type diff =
  | Deleted of sentence_id list
  | Added of pre_sentence list
  | Equal of (sentence_id * pre_sentence) list

  val diff : sentence list -> pre_sentence list -> diff list

  val string_of_diff : diff -> string

end = struct

  type t = {
    sentences_by_id : sentence SM.t;
    sentences_by_end : sentence LM.t;
    schedule : Scheduler.schedule;
  }

  let empty = {
    sentences_by_id = SM.empty;
    sentences_by_end = LM.empty;
    schedule = initial_schedule;
  }

  let to_string parsed =
    LM.fold (fun stop s acc -> acc ^ string_of_sentence s ^ "\n") parsed.sentences_by_end ""

  let schedule parsed = parsed.schedule

  let range_of_sentence raw sentence =
    let range_start = RawDoc.position_of_loc raw sentence.start in
    let range_end = RawDoc.position_of_loc raw sentence.stop in
    { range_start; range_end }

  let range_of_id raw parsed id =
    match SM.find_opt id parsed.sentences_by_id with
    | None -> CErrors.anomaly Pp.(str"Trying to get range of non-existing sentence " ++ Stateid.print id)
    | Some sentence -> range_of_sentence raw sentence

  let parsed_ranges raw parsed =
    SM.fold (fun _id sentence acc ->
      match sentence.ast with
      | ParseError _ -> acc
      | ValidAst _ -> range_of_sentence raw sentence :: acc)
      parsed.sentences_by_id
      []

  let make_diagnostic raw parsed id oloc message severity =
    let range =
      match oloc with
      | None -> range_of_id raw parsed id
      | Some loc ->
        RawDoc.range_of_loc raw loc
    in
    { range; message; severity }

  let parse_errors raw parsed =
    let collect_error id sentence acc =
      match sentence.ast with
      | ParseError (oloc, message) ->
        make_diagnostic raw parsed id oloc message Error :: acc
      | ValidAst _ -> acc
    in
    SM.fold collect_error parsed.sentences_by_id []

  let add_sentence parsed start stop ast parsing_state scheduler_state_before =
    let id = Stateid.fresh () in
    let scheduler_state_after, schedule =
      let oast =
        match ast with
        | ValidAst (ast,_tokens) -> Some ast
        | ParseError _ -> None
      in
      Scheduler.schedule_sentence (id,oast) scheduler_state_before parsed.schedule
    in
    (* FIXME may invalidate scheduler_state_XXX for following sentences -> propagate? *)
    let sentence = { start; stop; ast; id; parsing_state; scheduler_state_before; scheduler_state_after } in
    { sentences_by_end = LM.add stop sentence parsed.sentences_by_end;
      sentences_by_id = SM.add id sentence parsed.sentences_by_id;
      schedule
    }, scheduler_state_after

  let remove_sentence parsed id =
    match SM.find_opt id parsed.sentences_by_id with
    | None -> parsed
    | Some sentence ->
      let sentences_by_id = SM.remove id parsed.sentences_by_id in
      let sentences_by_end = LM.remove sentence.stop parsed.sentences_by_end in
      (* TODO clean up the schedule and free cached states *)
      { parsed with sentences_by_id; sentences_by_end }

  let remove_sentences_after parsed loc =
    log @@ "Removing sentences after loc " ^ string_of_int loc;
    let (before,ov,after) = LM.split loc parsed.sentences_by_end in
    let removed = Option.cata (fun v -> LM.add loc v after) after ov in
    let removed = LM.fold (fun _ sentence acc -> Stateid.Set.add sentence.id acc) removed Stateid.Set.empty in
    let sentences_by_id = Stateid.Set.fold (fun id m -> log @@ "Remove sentence (after) " ^ Stateid.to_string id; SM.remove id m) removed parsed.sentences_by_id in
    (* TODO clean up the schedule and free cached states *)
    { parsed with sentences_by_id; sentences_by_end = before}, removed

  let sentences_before parsed loc =
    let (before,ov,after) = LM.split loc parsed.sentences_by_end in
    let before = Option.cata (fun v -> LM.add loc v before) before ov in
    List.map (fun (_id,s) -> s) @@ LM.bindings before

  let sentences_after parsed loc =
    let (before,ov,after) = LM.split loc parsed.sentences_by_end in
    let after = Option.cata (fun v -> LM.add loc v after) after ov in
    List.map (fun (_id,s) -> s) @@ LM.bindings after

  let find_sentence parsed loc =
    match LM.find_first_opt (fun k -> loc <= k) parsed.sentences_by_end with
    | Some (_, sentence) when sentence.start <= loc -> Some sentence
    | _ -> None

  let find_sentence_before parsed loc =
    match LM.find_last_opt (fun k -> k <= loc) parsed.sentences_by_end with
    | Some (_, sentence) -> Some sentence
    | _ -> None

  let state_after_sentence exec = function
    | Some (stop, { parsing_state; scheduler_state_after; ast; id }) ->
      begin match ast with
      | ParseError _ ->
        Some (stop, parsing_state, scheduler_state_after)
      | ValidAst (ast, _tokens) ->
        begin match classify_vernac ast with
        | ParsingEffect ->
          begin match ExecutionManager.get_parsing_state_after exec id with
          | None -> None
          | Some parsing_state -> Some (stop, parsing_state, scheduler_state_after)
          end
        | StateEffect -> Some (stop, parsing_state, scheduler_state_after)
        end
      end
    | None -> Some (-1, Vernacstate.Parser.init (), Scheduler.initial_state)

  (** Returns the state at position [pos] if it does not require execution *)
  let state_at_pos parsed exec pos =
    state_after_sentence exec @@
      LM.find_last_opt (fun stop -> stop <= pos) parsed.sentences_by_end

  (** Returns the state at the end of [parsed] if it does not require execution *)
  let state_at_end parsed exec =
    state_after_sentence exec @@
      LM.max_binding_opt parsed.sentences_by_end

  let pos_at_end parsed =
    match LM.max_binding_opt parsed.sentences_by_end with
    | Some (stop, _) -> stop
    | None -> -1

  let split_sentences loc sentences =
    let (before,ov,after) = LM.split loc sentences in
    match ov with
    | Some v -> (before,Some (loc,v),after)
    | None ->
      begin match LM.min_binding_opt after with
      | Some (stop, { start } as b) when start <= loc -> (before, Some b, LM.remove stop after)
      | _ -> (before, None, after)
    end

  let shift_sentences parsed loc offset =
    let (before,ov,after) = split_sentences loc parsed.sentences_by_end in
    let res =
      match ov with
      | None -> before
      | Some (stop,v) when v.start >= loc ->
        LM.add (stop + offset) { v with start = v.start + offset; stop = v.stop + offset } before
      | Some (stop,v) ->
        LM.add (stop + offset) { v with stop = v.stop + offset } before
    in
    let sentences_by_end =
      LM.fold (fun stop v acc -> LM.add (stop + offset) { v with start = v.start + offset; stop = v.stop + offset } acc) after res
    in
    let shift_sentence s =
      if s.start >= loc then { s with start = s.start + offset; stop = s.stop + offset }
      else if s.stop >= loc then { s with stop = s.stop + offset }
      else s
    in
    let sentences_by_id = SM.map shift_sentence parsed.sentences_by_id in
    { parsed with sentences_by_end; sentences_by_id }

  let previous_sentence parsed id =
    let current = SM.find id parsed.sentences_by_id in
    Option.map snd @@ LM.find_last_opt (fun stop -> stop <= current.start) parsed.sentences_by_end

  let next_sentence parsed id =
    let current = SM.find id parsed.sentences_by_id in
    Option.map snd @@ LM.find_first_opt (fun stop -> stop > current.stop) parsed.sentences_by_end

  let executed_ranges raw parsed execution_state executed_loc =
    let valid_ids = List.map (fun s -> s.id) @@ sentences_before parsed executed_loc in
    let executed_ids = List.filter (ExecutionManager.is_executed execution_state) valid_ids in
    List.map (range_of_id raw parsed) executed_ids

  let patch_sentence parsed scheduler_state_before id ({ ast; start; stop } : pre_sentence) =
    log @@ "Patching sentence " ^ Stateid.to_string id;
    let old_sentence = SM.find id parsed.sentences_by_id in
    let scheduler_state_after, schedule =
      let oast =
        match ast with
        | ValidAst (ast,_tokens) -> Some ast
        | ParseError _ -> None
      in
      Scheduler.schedule_sentence (id,oast) scheduler_state_before parsed.schedule
    in
    let new_sentence = { old_sentence with ast; start; stop; scheduler_state_before; scheduler_state_after } in
    let sentences_by_id = SM.add id new_sentence parsed.sentences_by_id in
    let sentences_by_end = LM.remove old_sentence.stop parsed.sentences_by_end in
    let sentences_by_end = LM.add new_sentence.stop new_sentence sentences_by_end in
    { sentences_by_end; sentences_by_id; schedule }, scheduler_state_after

type diff =
  | Deleted of sentence_id list
  | Added of pre_sentence list
  | Equal of (sentence_id * pre_sentence) list

(* TODO improve diff strategy (insertions,etc) *)
let rec diff old_sentences new_sentences =
  match old_sentences, new_sentences with
  | [], [] -> []
  | [], new_sentences -> [Added new_sentences]
  | old_sentences, [] -> [Deleted (List.map (fun s -> s.id) old_sentences)]
    (* FIXME something special should be done when `Deleted` is applied to a parsing effect *)
  | old_sentence::old_sentences, new_sentence::new_sentences ->
    if same_tokens old_sentence new_sentence then
      Equal [(old_sentence.id,new_sentence)] :: diff old_sentences new_sentences
    else Deleted [old_sentence.id] :: Added [new_sentence] :: diff old_sentences new_sentences

let string_of_diff = function
  | Deleted ids -> "- " ^ String.concat "," (List.map Stateid.to_string ids)
  | Added sentences -> String.concat "\n" (List.map (fun (s : pre_sentence) -> "+ " ^ string_of_parsed_ast s.ast) sentences)
  | Equal l -> "= " ^ String.concat "," (List.map (fun (id,_) -> Stateid.to_string id) l)

end

type document = {
  parsed_loc : int;
  executed_loc : int option;
  raw_doc : RawDoc.t;
  parsed_doc : ParsedDoc.t;
  execution_state : ExecutionManager.state;
  more_to_parse : bool;
}

type progress_hook = document -> unit

let parsed_ranges doc = ParsedDoc.parsed_ranges doc.raw_doc doc.parsed_doc

let executed_ranges doc =
  match doc.executed_loc with
  | None -> []
  | Some loc ->
    ParsedDoc.executed_ranges doc.raw_doc doc.parsed_doc doc.execution_state loc

let diagnostics doc =
  let exec_errors = ExecutionManager.errors doc.execution_state in
  log @@ "exec errors in diags: " ^ string_of_int (List.length exec_errors);
  let mk_exec_diag (id,oloc,message) =
    ParsedDoc.make_diagnostic doc.raw_doc doc.parsed_doc id oloc message Error
  in
  let exec_diags = List.map mk_exec_diag exec_errors in
  ParsedDoc.parse_errors doc.raw_doc doc.parsed_doc @ exec_diags

let rec stream_tok n_tok acc (str,loc_fn) begin_line begin_char =
  let e = Stream.next str in
  if Tok.(equal e EOI) then
    List.rev acc
  else
    stream_tok (n_tok+1) (e::acc) (str,loc_fn) begin_line begin_char

let parse_one_sentence stream ~st =
  let pa = Pcoq.Parsable.make stream in
  Vernacstate.Parser.parse st (Pvernac.main_entry (Some (Vernacinterp.get_default_proof_mode ()))) pa
  (* FIXME: handle proof mode correctly *)

let rec junk_whitespace stream =
  match Stream.peek stream with
  | Some (' ' | '\t' | '\n' |'\r') ->
    Stream.junk stream; junk_whitespace stream
  | _ -> ()

let rec junk_sentence_end stream =
  match Stream.npeek 2 stream with
  | ['.'; (' ' | '\t' | '\n' |'\r')] -> Stream.junk stream
  | [] -> ()
  | _ ->  Stream.junk stream; junk_sentence_end stream

(** Parse until we need to execute more. *)
let rec parse_more parsing_state stream raw parsed =
  log "Parsing more";
  let handle_parse_error start msg =
    log @@ "handling parse error at " ^ string_of_int start;
    junk_sentence_end stream;
    let stop = Stream.count stream in
    let sentence = { ast = ParseError msg; start; stop; parsing_state } in
    let parsed = sentence :: parsed in
    parse_more parsing_state stream raw parsed
  in
  let start = Stream.count stream in
  begin try
    (* FIXME should we save lexer state? *)
    let oast = parse_one_sentence stream ~st:parsing_state in
    let stop = Stream.count stream in
    begin match oast with
    | None (* EOI *) -> List.rev parsed, false
    | Some ast ->
      log @@ "Parsed: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
      let begin_line, begin_char, end_char =
              match ast.loc with
              | Some lc -> lc.line_nb, lc.bp, lc.ep
              | None -> assert false
      in
      let str = String.sub (RawDoc.text raw) begin_char (end_char - begin_char) in
      let sstr = Stream.of_string str in
      let lex = CLexer.Lexer.tok_func sstr in
      let tokens = stream_tok 0 [] lex begin_line begin_char in
      let sentence = { ast = ValidAst(ast,tokens); start; stop; parsing_state } in
      let parsed = sentence :: parsed in
      match classify_vernac ast with
      | ParsingEffect -> (* parsing more would require execution *)
        List.rev parsed, true
      | StateEffect ->
        parse_more parsing_state stream raw parsed
    end
    with
    | Stream.Error msg as exn ->
      let loc = Loc.get_loc @@ Exninfo.info exn in
      handle_parse_error start (loc,msg)
    | CLexer.Error.E e as exn -> (* May be more problematic to handle for the diff *)
      let loc = Loc.get_loc @@ Exninfo.info exn in
      handle_parse_error start (loc,CLexer.Error.to_string e)
  end

let parse_more parsing_state stream raw =
  parse_more parsing_state stream raw []

let invalidate top_edit parsed_doc new_sentences exec_st =
  (** Algo:
  We parse the new doc from the topmost edit to the bottom one.
  - If execution is required, we invalidate everything after the parsing
  effect. Then we diff the truncated zone and invalidate execution states.
  - If the previous doc contained a parsing effect in the editted zone, we also invalidate.
  Otherwise, we diff the editted zone.
  We invalidate dependents of changed/removed/added sentences (according to
  both/old/new graphs). When we have to invalidate a parsing effect state, we
  invalidate the parsing after it.
   *)
   (* TODO optimize by reducing the diff to the modified zone *)
   (*
  let text = RawDoc.text current.raw_doc in
  let len = String.length text in
  let stream = Stream.of_string text in
  let parsed_current = parse_more len stream current.parsed_doc () in
  *)
  let rec invalidate_diff parsed_doc scheduler_state exec_st = let open ParsedDoc in function
    | [] -> exec_st, parsed_doc
    | Equal s :: diffs ->
      let patch_sentence (parsed_doc,scheduler_state) (old_s,new_s) =
        ParsedDoc.patch_sentence parsed_doc scheduler_state old_s new_s
      in
      let parsed_doc, scheduler_state = List.fold_left patch_sentence (parsed_doc, scheduler_state) s in
      invalidate_diff parsed_doc scheduler_state exec_st diffs
    | Deleted ids :: diffs ->
      let exec_st = List.fold_left (fun st id -> ExecutionManager.invalidate (ParsedDoc.schedule parsed_doc) id st) exec_st ids in
      let parsed_doc = List.fold_left ParsedDoc.remove_sentence parsed_doc ids in
      (* FIXME update scheduler state, maybe invalidate after diff zone *)
      invalidate_diff parsed_doc scheduler_state exec_st diffs
    | Added new_sentences :: diffs ->
    (* FIXME could have side effect on the following, unchanged sentences *)
      let add_sentence (parsed_doc,scheduler_state) ({ start; stop; ast; parsing_state } : pre_sentence) =
        ParsedDoc.add_sentence parsed_doc start stop ast parsing_state scheduler_state
      in
      let parsed_doc, scheduler_state = List.fold_left add_sentence (parsed_doc,scheduler_state) new_sentences in
      invalidate_diff parsed_doc scheduler_state exec_st diffs
  in
  let (_,_parsing_state,scheduler_state) = Option.get @@ ParsedDoc.state_at_pos parsed_doc exec_st top_edit in
  let old_sentences = ParsedDoc.sentences_after parsed_doc top_edit in
  let diff = ParsedDoc.diff old_sentences new_sentences in
  log @@ String.concat "\n" (List.map ParsedDoc.string_of_diff diff);
  invalidate_diff parsed_doc scheduler_state exec_st diff

(** Validate document when raw text has changed *)
let validate_document ({ parsed_loc; raw_doc; parsed_doc; execution_state } as document) =
  match ParsedDoc.state_at_pos parsed_doc execution_state parsed_loc with
  | None -> document
  | Some (stop, parsing_state, _scheduler_state) ->
    let text = RawDoc.text raw_doc in
    let stream = Stream.of_string text in
    while Stream.count stream < stop do Stream.junk stream done;
    log @@ Format.sprintf "Parsing more from pos %i" stop;
    let new_sentences, more_to_parse = parse_more parsing_state stream raw_doc (* TODO invalidate first *) in
    let execution_state, parsed_doc = invalidate (stop+1) document.parsed_doc new_sentences execution_state in
    let parsed_loc = ParsedDoc.pos_at_end parsed_doc in
    { document with parsed_doc; execution_state; more_to_parse; parsed_loc }

let create_document vernac_state text =
  let raw_doc = RawDoc.create text in
  let execution_state = ExecutionManager.init vernac_state in
  validate_document
    { parsed_loc = -1;
      executed_loc = None;
      raw_doc;
      parsed_doc = ParsedDoc.empty;
      more_to_parse = true;
      execution_state;
    }

let apply_text_edit document edit =
  let loc = RawDoc.loc_of_position document.raw_doc (fst edit).range_end in
  let raw_doc, offset = RawDoc.apply_text_edit document.raw_doc edit in
  log @@ "Edit offset " ^ string_of_int offset;
  let parsed_doc = ParsedDoc.shift_sentences document.parsed_doc loc offset in
  let execution_state = ExecutionManager.shift_locs document.execution_state loc offset in
  { document with raw_doc; parsed_doc; execution_state }

let apply_text_edits document edits =
  match edits with
  | [] -> document
  | _ ->
    let top_edit : int = RawDoc.loc_of_position document.raw_doc @@ top_edit_position edits in
    (* FIXME is top_edit_position correct with multiple edits? Shouldn't it be
       computed as part of the fold below? *)
    let document = List.fold_left apply_text_edit document edits in
    let parsed_loc = min top_edit document.parsed_loc in
    let executed_loc = Option.map (min parsed_loc) document.executed_loc in
    { document with parsed_loc; executed_loc }

let interpret_to_loc ~after ?(progress_hook=fun doc -> ()) doc loc =
  log @@ "Interpreting to loc " ^ string_of_int loc;
  let rec make_progress doc =
    let doc = validate_document doc in
    log @@ ParsedDoc.to_string doc.parsed_doc;
    (** We jump to the sentence before the position, otherwise jumping to the
    whitespace at the beginning of a sentence will observe the state after
    executing the sentence, which is unnatural. *)
    let find = if after then ParsedDoc.find_sentence else ParsedDoc.find_sentence_before in
    match find doc.parsed_doc loc with
    | None -> (* document is empty *) (doc, None)
    | Some { id; stop; start } ->
      let progress_hook st = progress_hook { doc with execution_state = st; executed_loc = Some stop } in
      let st = ExecutionManager.observe progress_hook (ParsedDoc.schedule doc.parsed_doc) id doc.execution_state in
      log @@ "Observed " ^ Stateid.to_string id;
      let doc = { doc with execution_state = st } in
      if doc.parsed_loc < loc && doc.more_to_parse then
        make_progress doc
      else
      let executed_loc = Some stop in
      let proof_data = match ExecutionManager.get_proofview st id with
        | None -> None
        | Some pv -> let pos = RawDoc.position_of_loc doc.raw_doc stop in Some (pv, pos)
      in
      { doc with executed_loc }, proof_data
  in
  make_progress doc

let interpret_to_position ?progress_hook doc pos =
  let loc = RawDoc.loc_of_position doc.raw_doc pos in
  interpret_to_loc ~after:false ?progress_hook doc loc

let interpret_to_previous doc =
  match doc.executed_loc with
  | None -> doc, None
  | Some loc ->
    interpret_to_loc ~after:false doc (loc-1)

let interpret_to_next doc =
  match doc.executed_loc with
  | None -> doc, None
  | Some stop ->
    interpret_to_loc ~after:true doc (stop+1)

let interpret_to_end ?progress_hook doc =
  interpret_to_loc ~after:false ?progress_hook doc (RawDoc.end_loc doc.raw_doc)

let reset vernac_state doc =
  let execution_state = ExecutionManager.init vernac_state in
  validate_document
    { doc with parsed_loc = -1;
      executed_loc = None;
      parsed_doc = ParsedDoc.empty;
      more_to_parse = true;
      execution_state;
    }
