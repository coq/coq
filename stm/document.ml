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

let debug_document = CDebug.create ~name:"document"

let log msg =
  if CDebug.get_debug_level "document" >= 2 then
  Format.eprintf "@[%s@]@\n%!" msg

module Position = struct

type t =
  { line : int;
    char : int;
  }

let compare pos1 pos2 =
  match Int.compare pos1.line pos2.line with
  | 0 -> Int.compare pos1.char pos2.char
  | x -> x

let to_string pos = Format.sprintf "(%i,%i)" pos.line pos.char

end

module Range = struct

type t =
  { start : Position.t;
    stop : Position.t;
  }

end

type text_edit = Range.t * string

let top_edit_position edits =
  match edits with
  | [] -> assert false
  | (Range.{ start },_) :: edits ->
    List.fold_left (fun min (Range.{ start },_) ->
    if Position.compare start min < 0 then start else min) start edits

let bottom_edit_position edits =
  match edits with
  | [] -> assert false
  | (Range.{ stop },_) :: edits ->
    List.fold_left (fun max (Range.{ stop },_) ->
    if Position.compare stop max > 0 then stop else max) stop edits

module RawDoc : sig

  type t

  val create : string -> t
  val text : t -> string

  val position_of_loc : t -> int -> Position.t
  val loc_of_position : t -> Position.t -> int
  val end_loc : t -> int

  val range_of_loc : t -> Loc.t -> Range.t

  val apply_text_edit : t -> text_edit -> t * int

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
    Position.{ line = !i - 1; char = loc - raw.lines.(!i - 1) }

  let loc_of_position raw Position.{ line; char } =
    raw.lines.(line) + char

  let end_loc raw =
    String.length raw.text

  let range_of_loc raw loc =
    let open Range in
    { start = position_of_loc raw loc.Loc.bp;
      stop = position_of_loc raw loc.Loc.ep;
    }

  type edit = Range.t * string

  let apply_text_edit raw (Range.{start; stop}, editText) =
    let start = loc_of_position raw start in
    let stop = loc_of_position raw stop in
    let before = String.sub raw.text 0 start in
    let after = String.sub raw.text stop (String.length raw.text - stop) in
    let new_text = before ^ editText ^ after in (* FIXME avoid concatenation *)
    let new_lines = compute_lines new_text in (* FIXME compute this incrementally *)
    let old_length = stop - start in
    let shift = String.length editText - old_length in
    { text = new_text; lines = new_lines }, shift

end

module LM = Map.Make (Int)

type sentence_id = Stateid.t

module SM = Map.Make (Stateid)

type parsed_ast =
  | ValidAst of ast * Tok.t list
  | ParseError of string Loc.located

(*
let classify_parsed_vernac = function
  | ValidAst (ast,_tokens) -> Vernac_classifier.classify_vernac ast
  | ParseError _ -> StateEffect (* Optimistic error recovery *)
  *)

let string_of_parsed_ast = function
  | ValidAst (ast,tokens) -> (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^ " [" ^ String.concat "--" (List.map (Tok.extract_string false) tokens) ^ "]"
  | ParseError _ -> "(parse error)"

type pre_sentence = {
  start : int;
  stop : int;
  parsing_state : Vernacstate.Parser.t; (* st used to parse this sentence *)
  ast : parsed_ast;
}

type sentence = {
  start : int;
  stop : int;
  parsing_state : Vernacstate.Parser.t; (* st used to parse this sentence *)
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


module ParsedDoc : sig

  type t

  val empty : t

  val to_string : t -> string

  val schedule : t -> schedule

  val parsed_ranges : RawDoc.t -> t -> Range.t list
  (*
  val executed_ranges : RawDoc.t -> t -> ExecutionManager.state -> int -> range list
  *)
(*
  val make_diagnostic : RawDoc.t -> t -> sentence_id -> Loc.t option -> string -> severity -> diagnostic
  *)

  val parse_errors : RawDoc.t -> t -> (Stateid.t * Loc.t option * string) list

  val add_sentence : t -> int -> int -> parsed_ast -> Vernacstate.Parser.t -> Scheduler.state -> t * Scheduler.state
  val remove_sentence : t -> sentence_id -> t
  val remove_sentences_after : t -> int -> t * Stateid.Set.t
  val sentences : t -> sentence list
  val sentences_before : t -> int -> sentence list
  val sentences_after : t -> int -> sentence list
  val get_sentence : t -> sentence_id -> sentence option
  val find_sentence : t -> int -> sentence option
  val find_sentence_before : t -> int -> sentence option
  val shift_sentences : t -> int -> int -> t

  val previous_sentence : t -> sentence_id -> sentence option
  val next_sentence : t -> sentence_id -> sentence option

  val pos_at_end : t -> int
  val state_at_end : parsing_state_hook:(sentence_id -> Vernacstate.Parser.t option) -> t -> (int * Vernacstate.Parser.t * Scheduler.state) option
  val state_at_pos : parsing_state_hook:(sentence_id -> Vernacstate.Parser.t option) -> t -> int -> (int * Vernacstate.Parser.t * Scheduler.state) option

  val patch_sentence : t -> Scheduler.state -> sentence_id -> pre_sentence -> t * Scheduler.state

  type diff =
  | Deleted of sentence_id list
  | Added of pre_sentence list
  | Equal of (sentence_id * pre_sentence) list

  val diff : sentence list -> pre_sentence list -> diff list

  val string_of_diff : diff -> string

  val range_of_id : RawDoc.t -> t -> Stateid.t -> Range.t

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
    let start = RawDoc.position_of_loc raw sentence.start in
    let stop = RawDoc.position_of_loc raw sentence.stop in
    Range.{ start; stop }

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

  let parse_errors raw parsed =
    let collect_error id sentence acc =
      match sentence.ast with
      | ParseError (oloc, message) ->
        (id, oloc, message) :: acc
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

  let sentences parsed =
    List.map snd @@ SM.bindings parsed.sentences_by_id

  let sentences_before parsed loc =
    let (before,ov,after) = LM.split loc parsed.sentences_by_end in
    let before = Option.cata (fun v -> LM.add loc v before) before ov in
    List.map (fun (_id,s) -> s) @@ LM.bindings before

  let sentences_after parsed loc =
    let (before,ov,after) = LM.split loc parsed.sentences_by_end in
    let after = Option.cata (fun v -> LM.add loc v after) after ov in
    List.map (fun (_id,s) -> s) @@ LM.bindings after

  let get_sentence parsed id =
    SM.find_opt id parsed.sentences_by_id

  let find_sentence parsed loc =
    match LM.find_first_opt (fun k -> loc <= k) parsed.sentences_by_end with
    | Some (_, sentence) when sentence.start <= loc -> Some sentence
    | _ -> None

  let find_sentence_before parsed loc =
    match LM.find_last_opt (fun k -> k <= loc) parsed.sentences_by_end with
    | Some (_, sentence) -> Some sentence
    | _ -> None

  let state_after_sentence ~parsing_state_hook = function
    | Some (stop, { parsing_state; scheduler_state_after; ast; id }) ->
      begin match ast with
      | ParseError _ ->
        Some (stop, parsing_state, scheduler_state_after)
      | ValidAst (ast, _tokens) ->
        begin match classify_vernac ast with
        | ParsingEffect ->
          begin match parsing_state_hook id with
          | None -> None
          | Some parsing_state -> Some (stop, parsing_state, scheduler_state_after)
          end
        | StateEffect -> Some (stop, parsing_state, scheduler_state_after)
        end
      end
    | None -> Some (-1, Vernacstate.Parser.init (), Scheduler.initial_state)

  (** Returns the state at position [pos] if it does not require execution *)
  let state_at_pos ~parsing_state_hook parsed pos =
    state_after_sentence ~parsing_state_hook @@
      LM.find_last_opt (fun stop -> stop <= pos) parsed.sentences_by_end

  (** Returns the state at the end of [parsed] if it does not require execution *)
  let state_at_end ~parsing_state_hook parsed =
    state_after_sentence ~parsing_state_hook @@
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
  id : int;
  parsed_loc : int;
  raw_doc : RawDoc.t;
  parsed_doc : ParsedDoc.t;
  more_to_parse : bool;
}

let id_of_doc doc = doc.id

type parsing_state_hook = sentence_id -> Vernacstate.Parser.t option

let parsed_ranges doc = ParsedDoc.parsed_ranges doc.raw_doc doc.parsed_doc

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

let invalidate ~parsing_state_hook top_edit parsed_doc new_sentences =
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
  let rec invalidate_diff parsed_doc scheduler_state invalid_ids = let open ParsedDoc in function
    | [] -> invalid_ids, parsed_doc
    | Equal s :: diffs ->
      let patch_sentence (parsed_doc,scheduler_state) (old_s,new_s) =
        ParsedDoc.patch_sentence parsed_doc scheduler_state old_s new_s
      in
      let parsed_doc, scheduler_state = List.fold_left patch_sentence (parsed_doc, scheduler_state) s in
      invalidate_diff parsed_doc scheduler_state invalid_ids diffs
    | Deleted ids :: diffs ->
      let invalid_ids = List.fold_left (fun ids id -> Stateid.Set.add id ids) invalid_ids ids in
      let parsed_doc = List.fold_left ParsedDoc.remove_sentence parsed_doc ids in
      (* FIXME update scheduler state, maybe invalidate after diff zone *)
      invalidate_diff parsed_doc scheduler_state invalid_ids diffs
    | Added new_sentences :: diffs ->
    (* FIXME could have side effect on the following, unchanged sentences *)
      let add_sentence (parsed_doc,scheduler_state) ({ start; stop; ast; parsing_state } : pre_sentence) =
        ParsedDoc.add_sentence parsed_doc start stop ast parsing_state scheduler_state
      in
      let parsed_doc, scheduler_state = List.fold_left add_sentence (parsed_doc,scheduler_state) new_sentences in
      invalidate_diff parsed_doc scheduler_state invalid_ids diffs
  in
  let (_,_parsing_state,scheduler_state) = Option.get @@ ParsedDoc.state_at_pos ~parsing_state_hook parsed_doc top_edit in
  let old_sentences = ParsedDoc.sentences_after parsed_doc top_edit in
  let diff = ParsedDoc.diff old_sentences new_sentences in
  log @@ String.concat "\n" (List.map ParsedDoc.string_of_diff diff);
  invalidate_diff parsed_doc scheduler_state Stateid.Set.empty diff

(** Validate document when raw text has changed *)
let validate_document ~parsing_state_hook ({ parsed_loc; raw_doc; parsed_doc } as document) =
  match ParsedDoc.state_at_pos ~parsing_state_hook parsed_doc parsed_loc with
  | None -> Stateid.Set.empty, document
  | Some (stop, parsing_state, _scheduler_state) ->
    let text = RawDoc.text raw_doc in
    let stream = Stream.of_string text in
    while Stream.count stream < stop do Stream.junk stream done;
    log @@ Format.sprintf "Parsing more from pos %i" stop;
    let new_sentences, more_to_parse = parse_more parsing_state stream raw_doc (* TODO invalidate first *) in
    let invalid_ids, parsed_doc = invalidate ~parsing_state_hook (stop+1) document.parsed_doc new_sentences in
    let parsed_loc = ParsedDoc.pos_at_end parsed_doc in
    invalid_ids, { document with parsed_doc; more_to_parse; parsed_loc }

let create_document ~id text =
  let raw_doc = RawDoc.create text in
  snd @@ validate_document ~parsing_state_hook:(fun _ -> None)
    { id;
      parsed_loc = -1;
      raw_doc;
      parsed_doc = ParsedDoc.empty;
      more_to_parse = true;
    }

let apply_text_edit document edit =
  let loc = RawDoc.loc_of_position document.raw_doc (fst edit).Range.stop in
  let raw_doc, offset = RawDoc.apply_text_edit document.raw_doc edit in
  log @@ "Edit offset " ^ string_of_int offset;
  let parsed_doc = ParsedDoc.shift_sentences document.parsed_doc loc offset in
  (*
  let execution_state = ExecutionManager.shift_locs document.execution_state loc offset in
  *)
  { document with raw_doc; parsed_doc }

let apply_text_edits document edits =
  match edits with
  | [] -> document
  | _ ->
    let top_edit : int = RawDoc.loc_of_position document.raw_doc @@ top_edit_position edits in
    (* FIXME is top_edit_position correct with multiple edits? Shouldn't it be
       computed as part of the fold below? *)
    let document = List.fold_left apply_text_edit document edits in
    let parsed_loc = min top_edit document.parsed_loc in
    (*
    let executed_loc = Option.map (min parsed_loc) document.executed_loc in
    *)
    { document with parsed_loc }

let get_sentence doc id = ParsedDoc.get_sentence doc.parsed_doc id
let find_sentence doc loc = ParsedDoc.find_sentence doc.parsed_doc loc
let find_sentence_before doc loc = ParsedDoc.find_sentence_before doc.parsed_doc loc

let more_to_parse doc = doc.more_to_parse
let parsed_loc doc = doc.parsed_loc
let schedule doc = ParsedDoc.schedule doc.parsed_doc

let position_of_loc doc = RawDoc.position_of_loc doc.raw_doc
let loc_of_position doc = RawDoc.loc_of_position doc.raw_doc
let end_loc doc = RawDoc.end_loc doc.raw_doc

let range_of_id doc id = ParsedDoc.range_of_id doc.raw_doc doc.parsed_doc id
let range_of_loc doc loc = RawDoc.range_of_loc doc.raw_doc loc
let parse_errors doc = ParsedDoc.parse_errors doc.raw_doc doc.parsed_doc
let sentences doc = ParsedDoc.sentences doc.parsed_doc
let sentences_before doc loc = ParsedDoc.sentences_before doc.parsed_doc loc
