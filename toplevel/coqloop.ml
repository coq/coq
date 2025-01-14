(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp

let print_emacs = ref false

let top_stderr x =
  Format.fprintf !Topfmt.err_ft "@[%a@]%!" pp_with x

(* A buffer for the character read from a channel. We store the command
 * entered to be able to report errors without pretty-printing. *)

type input_buffer = {
  mutable prompt : Stm.doc -> string;
  mutable str : Bytes.t; (* buffer of already read characters *)
  mutable len : int;    (* number of chars in the buffer *)
  mutable bols : int list; (* offsets in str of beginning of lines *)
  mutable stream : (unit,char) Gramlib.Stream.t; (* stream of chars *)
  mutable tokens : Procq.Parsable.t; (* stream of tokens *)
  mutable start : int } (* stream count of the first char of the buffer *)

(* Double the size of the buffer. *)

let resize_buffer ibuf = let open Bytes in
  let nstr = create (2 * length ibuf.str + 1) in
  blit ibuf.str 0 nstr 0 (length ibuf.str);
  ibuf.str <- nstr

let peek_to_newline ibuf =
  (* peek to see a newline following the latest command
     cf #19355 *)
  let rec aux n =
    let l = Gramlib.Stream.npeek () n ibuf.stream in
    if List.length l < n then ()
    else match CList.last l with
      | '\n' -> ()
      | ' ' | '\t' -> aux (n+1)
      | _ -> (* nonblank character: the latest command is not the last on this line *) ()
  in
  aux 1

(* Delete all irrelevant lines of the input buffer. Keep the last line
   in the buffer (useful when there are several commands on the same line). *)
let resynch_buffer ibuf =
  let () = peek_to_newline ibuf in
  match ibuf.bols with
    | ll::_ ->
        let new_len = ibuf.len - ll in
        Bytes.blit ibuf.str ll ibuf.str 0 new_len;
        ibuf.len <- new_len;
        ibuf.bols <- [];
        ibuf.start <- ibuf.start + ll
    | _ -> ()


(* emacs special prompt tag for easy detection. No special character,
   to avoid interfering with utf8. Compatibility code removed. *)
let emacs_prompt_startstring () = if !print_emacs then "<prompt>"  else ""
let emacs_prompt_endstring   () = if !print_emacs then "</prompt>" else ""

(* Read a char in an input channel, displaying a prompt at every
   beginning of line. *)
let prompt_char doc ic ibuf () =
  let bol = match ibuf.bols with
    | ll::_ -> Int.equal ibuf.len ll
    | [] -> Int.equal ibuf.len 0
  in
  if bol && not !print_emacs then top_stderr (str (ibuf.prompt doc));
  try
    let c = input_char ic in
    if c == '\n' then ibuf.bols <- (ibuf.len+1) :: ibuf.bols;
    if ibuf.len == Bytes.length ibuf.str then resize_buffer ibuf;
    Bytes.set ibuf.str ibuf.len c;
    ibuf.len <- ibuf.len + 1;
    Some c
  with End_of_file ->
    None

(* Functions to print underlined locations from an input buffer. *)
module TopErr = struct

(* Given a location, returns the list of locations of each line. The last
   line is returned separately. It also checks the location bounds. *)

let get_bols_of_loc ibuf (bp,ep) =
  let add_line (b,e) lines =
    if b < 0 || e < b then CErrors.anomaly (Pp.str "Bad location.");
    match lines with
      | ([],None) -> ([], Some (b,e))
      | (fl,oe) -> ((b,e)::fl, oe)
  in
  let rec lines_rec ba after = function
    | []                  -> add_line (0,ba) after
    | ll::_ when ll <= bp -> add_line (ll,ba) after
    | ll::fl              ->
        let nafter = if ll < ep then add_line (ll,ba) after else after in
        lines_rec ll nafter fl
  in
  let bols = match ibuf.bols with
    | [] -> [ibuf.len+1] (* no newline at the end of the command, pretend there was one *)
    | _ :: _ as bols -> bols
  in
  let (fl,ll) = lines_rec ibuf.len ([],None) bols in
  (fl,Option.get ll)

let dotted_location (b,e) =
  if e-b < 3 then
    ("", String.make (e-b) ' ')
  else
    (String.make (e-b-1) '.', " ")

let blanch_utf8_string s bp ep = let open Bytes in
  let s' = make (ep-bp) ' ' in
  let j = ref 0 in
  for i = bp to ep - 1 do
    let n = Char.code (get s i) in
    (* Heuristic: assume utf-8 chars are printed using a single
    fixed-size char and therefore contract all utf-8 code into one
    space; in any case, preserve tabulation so
    that its effective interpretation in terms of spacing is preserved *)
    if get s i == '\t' then set s' !j '\t';
    if n < 0x80 || 0xC0 <= n then incr j
  done;
  Bytes.sub_string s' 0 !j

let adjust_loc_buf ib loc = let open Loc in
  { loc with ep = loc.ep - ib.start; bp = loc.bp - ib.start }

let print_highlight_location ib loc =
  let (bp,ep) = Loc.unloc loc in
  let highlight_lines =
    match get_bols_of_loc ib (bp,ep) with
      | ([],(bl,el)) ->
          let shift = blanch_utf8_string ib.str bl bp in
          let span = String.length (blanch_utf8_string ib.str bp ep) in
          (str"> " ++ str(Bytes.sub_string ib.str bl (el-bl-1)) ++ fnl () ++
           str"> " ++ str(shift) ++ str(String.make span '^'))
      | ((b1,e1)::ml,(bn,en)) ->
          let (d1,s1) = dotted_location (b1,bp) in
          let (dn,sn) = dotted_location (ep,en) in
          let l1 = (str"> " ++ str d1 ++ str s1 ++
                      str(Bytes.sub_string ib.str bp (e1-bp))) in
          let li =
            prlist (fun (bi,ei) ->
                      (str"> " ++ str(Bytes.sub_string ib.str bi (ei-bi)))) ml in
          let ln = (str"> " ++ str(Bytes.sub_string ib.str bn (ep-bn)) ++
                      str sn ++ str dn) in
          (l1 ++ li ++ ln)
  in
  highlight_lines

let valid_buffer_loc ib loc =
  let (b,e) = Loc.unloc loc in b-ib.start >= 0 && e-ib.start <= ib.len && b<=e

(* Toplevel error explanation. *)
let error_info_for_buffer ?loc buf =
  match loc with
  | None -> Topfmt.pr_phase ?loc ()
  | Some loc ->
      let fname = loc.Loc.fname in
        (* We are in the toplevel *)
      match fname with
      | Loc.ToplevelInput ->
        let nloc = adjust_loc_buf buf loc in
        if valid_buffer_loc buf loc then
          match Topfmt.pr_phase ~loc:nloc () with
          | None -> None
          | Some hd -> Some (hd ++ fnl () ++ print_highlight_location buf nloc)
        (* in the toplevel, but not a valid buffer *)
        else Topfmt.pr_phase ~loc ()
      (* we are in batch mode, don't adjust location *)
      | Loc.InFile _ -> Topfmt.pr_phase ~loc ()

(* Actual printing routine *)
let print_error_for_buffer ?loc ?qf lvl msg buf =
  let pre_hdr = error_info_for_buffer ?loc buf in
  if !print_emacs
  then Topfmt.emacs_logger ?pre_hdr lvl msg
  else Topfmt.std_logger   ?pre_hdr ?qf lvl msg

(*
let print_toplevel_parse_error (e, info) buf =
  let loc = Loc.get_loc info in
  let lvl = Feedback.Error in
  let msg = CErrors.iprint (e, info) in
  print_error_for_buffer ?loc lvl msg buf
*)
end

(*s The Rocq prompt is the name of the focused proof, if any, and "Rocq"
    otherwise. We trap all exceptions to prevent the error message printing
    from cycling. *)
let make_prompt () =
  try
    (Names.Id.to_string (Vernacstate.Declare.get_current_proof_name ())) ^ " < "
  with Vernacstate.Declare.NoCurrentProof ->
    "Rocq < "
  [@@ocaml.warning "-3"]

(* the rocq prompt added to the default one when in emacs mode
   The prompt contains the current state label [n] (for global
   backtracking) and the current proof state [p] (for proof
   backtracking) plus the list of open (nested) proofs (for proof
   aborting when backtracking). It looks like:

   "n |lem1|lem2|lem3| p < "
*)
let make_emacs_prompt doc =
  let statnum = Stateid.to_string (Stm.get_current_state ~doc) in
  let dpth = Stm.current_proof_depth ~doc in
  let pending = Stm.get_all_proof_names ~doc in
  let pendingprompt =
    List.fold_left
      (fun acc x -> acc ^ (if CString.is_empty acc then "" else "|") ^ Names.Id.to_string x)
      "" pending in
  let proof_info = if dpth >= 0 then string_of_int dpth else "0" in
  if !print_emacs then statnum ^ " |" ^ pendingprompt ^ "| " ^ proof_info ^ " < "
  else ""

(* A buffer to store the current command read on stdin. It is
 * initialized when a vernac command is immediately followed by "\n",
 * or after a Drop. *)
let top_buffer =
  let pr doc =
    emacs_prompt_startstring()
    ^ make_prompt()
    ^ make_emacs_prompt doc
    ^ emacs_prompt_endstring()
  in
  let stream = Gramlib.Stream.empty () in
  { prompt = pr;
    str = Bytes.empty;
    len = 0;
    bols = [];
    stream;
    tokens = Procq.Parsable.make stream;
    start = 0 }

(* Intialize or reinitialize the char stream *)
let reset_input_buffer ~state =
  let stream = Gramlib.Stream.from (prompt_char state.Vernac.State.doc stdin top_buffer) in
  top_buffer.str <- Bytes.empty;
  top_buffer.len <- 0;
  top_buffer.bols <- [];
  top_buffer.stream <- stream;
  top_buffer.tokens <- Procq.Parsable.make stream;
  top_buffer.start <- 0

let set_prompt prompt =
  top_buffer.prompt
  <- (fun doc ->
    emacs_prompt_startstring()
    ^ prompt ()
    ^ emacs_prompt_endstring())

(* Read the input stream until a dot is encountered *)
let parse_to_dot =
  let rec dot kwstate st = match Gramlib.LStream.next kwstate st with
    | Tok.KEYWORD ("."|"...") -> ()
    | Tok.EOI -> ()
    | _ -> dot kwstate st
  in
  Procq.Entry.(of_parser "Coqtoplevel.dot" { parser_fun = dot })

(* If an error occurred while parsing, we try to read the input until a dot
   token is encountered.
   We assume that when a lexer error occurs, at least one char was eaten *)

let rec discard_to_dot () =
  try
    Procq.Entry.parse parse_to_dot top_buffer.tokens
  with
    | CLexer.Error.E _ -> (* Lexer failed *) discard_to_dot ()
    | e when CErrors.noncritical e -> ()

let read_sentence ~state input =
  (* XXX: careful with ignoring the state Eugene!*)
  let open Vernac.State in
  try Stm.parse_sentence ~doc:state.doc state.sid ~entry:G_toplevel.vernac_toplevel input
  with reraise ->
    let reraise = Exninfo.capture reraise in
    (* When typing Ctrl-C, two situations may arise:
       - if a lexer/parsing arrived first, the rest of the ill-formed
         sentence needs to be discarded, and, if Ctrl-C is found while
         trying to discarding (in discard_to_dot), let it bypass the
         reporting of the parsing error and report the Sys.Break
         instead.
       - if a Ctrl-C arrives after a valid start of sentence, do not
         discard_to_dot since Ctrl-C is the last read character and
         there is nothing left to discard. *)
    (match fst reraise with
     | Sys.Break -> Pp.pp_with !Topfmt.err_ft (Pp.fnl ())
     | _ ->
        try discard_to_dot ()
        with Sys.Break ->
          Pp.pp_with !Topfmt.err_ft (Pp.fnl ());
          raise Sys.Break);
    (* The caller of read_sentence does the error printing now, this
       should be re-enabled once we rely on the feedback error
       printer again *)
    (* TopErr.print_toplevel_parse_error reraise top_buffer; *)
    Exninfo.iraise reraise

let extract_default_loc loc doc_id sid : Loc.t option =
  match loc with
  | Some _ -> loc
  | None ->
    try
      let doc = Stm.get_doc doc_id in
      Option.cata (fun {CAst.loc} -> loc) None Stm.(get_ast ~doc sid)
    with _ -> loc

(** Coqloop Console feedback handler *)
let coqloop_feed (fb : Feedback.feedback) = let open Feedback in
  match fb.contents with
  | Processed   -> ()
  | Incomplete  -> ()
  | Complete    -> ()
  | ProcessingIn _ -> ()
  | InProgress _ -> ()
  | WorkerStatus (_,_) -> ()
  | AddedAxiom  -> ()
  | GlobRef (_,_,_,_,_) -> ()
  | GlobDef (_,_,_,_) -> ()
  | FileDependency (_,_) -> ()
  | FileLoaded (_,_) -> ()
  | Custom (_,_,_) -> ()
  (* Re-enable when we switch back to feedback-based error printing *)
  | Message (Error,loc,_,msg) -> ()
  (* TopErr.print_error_for_buffer ?loc lvl msg top_buffer *)
  | Message (Warning,loc,qf,msg) ->
    let loc = extract_default_loc loc fb.doc_id fb.span_id in
    TopErr.print_error_for_buffer ?loc ~qf Warning msg top_buffer
  | Message (lvl,loc,qf,msg) ->
    TopErr.print_error_for_buffer ?loc ~qf lvl msg top_buffer

(** Main rocq loop : read vernacular expressions until Drop is entered.
    Ctrl-C is handled internally as Sys.Break instead of aborting Rocq.
    Normally, the only exceptions that can come out of [do_vernac] and
    exit the loop are Drop and Quit. Any other exception there indicates
    an issue with [print_toplevel_error] above. *)

(* Flush in a compatible order with 8.5 *)
(* This mimics the semantics of the old Pp.flush_all *)
let loop_flush_all () =
  flush stderr;
  flush stdout;
  Format.pp_print_flush !Topfmt.std_ft ();
  Format.pp_print_flush !Topfmt.err_ft ()

(* Goal equality heuristic. *)
let pequal cmp1 cmp2 (a1,a2) (b1,b2) = cmp1 a1 b1 && cmp2 a2 b2
let evleq e1 e2 = CList.equal Evar.equal e1 e2
let cproof p1 p2 =
  let Proof.{goals=a1;stack=a2;sigma=sigma1} = Proof.data p1 in
  let Proof.{goals=b1;stack=b2;sigma=sigma2} = Proof.data p2 in
  evleq a1 b1 &&
  CList.equal (pequal evleq evleq) a2 b2 &&
  CList.equal Evar.equal (Evd.shelf sigma1) (Evd.shelf sigma2) &&
  Evar.Set.equal (Evd.given_up sigma1) (Evd.given_up sigma2)

(* todo: could add other Set/Unset commands, such as "Printing Universes" *)
let print_anyway_opts = [
  [ "Diffs" ];
  ]

let print_anyway c =
  let open Vernacexpr in
  match c.expr with
  | VernacSynterp (VernacSetOption (_, opt, _)) -> List.mem opt print_anyway_opts
  | _ -> false

(* print the proof step, possibly with diffs highlighted, *)
let print_and_diff oldp proof =
  let output =
    if Proof_diffs.show_diffs () then
      try Printer.pr_open_subgoals ~diffs:oldp proof
      with Pp_diff.Diff_Failure msg -> begin
        (* todo: print the unparsable string (if we know it) *)
        Feedback.msg_warning Pp.(str ("Diff failure: " ^ msg) ++ cut()
            ++ str "Showing results without diff highlighting" );
        Printer.pr_open_subgoals proof
      end
    else
      Printer.pr_open_subgoals proof
  in
  Feedback.msg_notice output

(* We try to behave better when goal printing raises an exception
   [usually Ctrl-C]

   This is mostly a hack as we should protect printing in a more
   generic way, but that'll do for now *)
let top_goal_print ~doc c oldp newp =
  try
    let proof_changed = not (Option.equal cproof oldp (Some newp)) in
    let print_goals = proof_changed && Vernacstate.Declare.there_are_pending_proofs () ||
                      print_anyway c in
    if not !Flags.quiet && print_goals then begin
      let dproof = Stm.get_prev_proof ~doc (Stm.get_current_state ~doc) in
      print_and_diff dproof newp
    end
  with
  | exn ->
    let (e, info) = Exninfo.capture exn in
    let loc = Loc.get_loc info in
    let msg = CErrors.iprint (e, info) in
    TopErr.print_error_for_buffer ?loc Feedback.Error msg top_buffer
  [@@ocaml.warning "-3"]

let { Goptions.get = exit_on_error } =
  let open Goptions in
  declare_bool_option_and_ref
    ~key:["Coqtop";"Exit";"On";"Error"]
    ~value:false
    ()

let show_proof_diff_cmd ~state diff_opt =
  let open Vernac.State in
  match state.proof with
  | None -> CErrors.user_err (str "No proofs to diff.")
  | Some proof ->
      let old = Stm.get_prev_proof ~doc:state.doc state.sid in
      Proof_diffs.diff_proofs ~diff_opt ?old proof

let ml_toplevel_state = ref None
let ml_toplevel_include_ran = ref false

(* Initialises the Ocaml toplevel before launching it, so that it can
   find the "include" file in the *source* directory *)
let init_ocaml_path () =
  let env = Boot.Env.init () in
  let corelib = Boot.Env.corelib env |> Boot.Path.to_string in
  let add_subdir dl = Mltop.add_ml_dir (Filename.concat corelib dl) in
  List.iter add_subdir ("dev" :: Coq_config.all_src_dirs)

let init_and_run_ml_toploop () =
  init_ocaml_path ();
  Flags.with_option Flags.in_ml_toplevel (Mltop.ocaml_toploop ~init_file:"ml_toplevel/include") ()

(* We return whether the execution should continue and a new state *)
let process_toplevel_command ~state stm =
  let open Vernac.State in
  let open G_toplevel in
  match stm with
  | VernacDrop ->
    if Mltop.is_ocaml_top() then begin
      (* Save the last state for [go ()] *)
      ml_toplevel_state := Some state;
      (* Initialise and launch the OCaml toplevel *)
      init_and_run_ml_toploop ();
      (* Reinitialize the char stream *)
      reset_input_buffer ~state;
      (* [go ()] was potentially executed — get the new state *)
      let state = Option.get !ml_toplevel_state in
      true, state
    end else begin
      Feedback.msg_warning (str "There is no ML toplevel.");
      true, state
    end

  | VernacBackTo bid ->
    let bid = Stateid.of_int bid in
    let doc, res = Stm.edit_at ~doc:state.doc bid in
    assert (res = Stm.NewTip);
    true, { state with doc; sid = bid }

  | VernacQuit ->
    false, state

  | VernacControl { CAst.loc; v=c } ->
    let nstate = Vernac.process_expr ~state (CAst.make ?loc c) in
    let () = match nstate.proof with
    | None -> ()
    | Some proof -> top_goal_print ~doc:state.doc c state.proof proof
    in
    true, nstate

  | VernacShowGoal { gid; sid } ->
    let proof = Stm.get_proof ~doc:state.doc (Stateid.of_int sid) in
    let goal = Printer.pr_goal_emacs ~proof gid sid in
    let () = Feedback.msg_notice goal in
    true, state

  | VernacShowProofDiffs diff_opt ->
    (* We print nothing if there are no goals left *)
    if not (Proof_diffs.color_enabled ()) then
      CErrors.user_err Pp.(str "Show Proof Diffs requires setting the \"-color\" command line argument to \"on\" or \"auto\".")
    else
      let out = show_proof_diff_cmd ~state diff_opt in
      Feedback.msg_notice out;
    true, state

let read_and_execute ~state =
  try
    let input = top_buffer.tokens in
    match read_sentence ~state input with
    | Some stm ->
      process_toplevel_command ~state stm
    (* End of file *)
    | None ->
      top_stderr (fnl ());
      false, state
  with
  (* Exception printing should be done by the feedback listener,
     however this is not yet ready so we rely on the exception for
     now. *)
  | Sys_blocked_io ->
    (* the parser doesn't like nonblocking mode, cf #10918 *)
    let msg =
      Pp.(strbrk "Coqtop needs the standard input to be in blocking mode." ++ spc()
          ++ str "One way of clearing the non-blocking flag is through Python:" ++ fnl()
          ++ str "  import os" ++ fnl()
          ++ str "  os.set_blocking(0, True)")
    in
    TopErr.print_error_for_buffer Feedback.Error msg top_buffer;
    exit 1
  | any ->
    let (e, info) = Exninfo.capture any in
    let loc = Loc.get_loc info in
    let msg = CErrors.iprint (e, info) in
    TopErr.print_error_for_buffer ?loc Feedback.Error msg top_buffer;
    if exit_on_error () then exit 1;
    true, state

let loop ~state =
  (* Initialize buffer *)
  reset_input_buffer ~state;
  Flags.without_option Flags.in_ml_toplevel (fun () ->
    (* The main loop, as a tail-recursive function *)
    let rec aux state =
      loop_flush_all ();
      top_stderr (fnl());
      let open Vernac.State in
      if !print_emacs then top_stderr (str (top_buffer.prompt state.doc));
      resynch_buffer top_buffer;
      let new_running, new_state = read_and_execute ~state:state in
      if new_running then
        (aux [@ocaml.tailcall]) new_state
      else
        new_state in
    aux state
  ) ()

let run ~opts ~state =
  let open Coqargs in
  print_emacs := opts.config.print_emacs;
  (* We initialize the console only if we run the toploop_run *)
  let tl_feed = Feedback.add_feeder coqloop_feed in
  let _ : Vernac.State.t = loop ~state in
  Feedback.del_feeder tl_feed
