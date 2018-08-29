(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
  mutable tokens : Pcoq.Parsable.t; (* stream of tokens *)
  mutable start : int } (* stream count of the first char of the buffer *)

(* Double the size of the buffer. *)

let resize_buffer ibuf = let open Bytes in
  let nstr = create (2 * length ibuf.str + 1) in
  blit ibuf.str 0 nstr 0 (length ibuf.str);
  ibuf.str <- nstr

(* Delete all irrelevant lines of the input buffer. Keep the last line
   in the buffer (useful when there are several commands on the same line). *)

let resynch_buffer ibuf =
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
let prompt_char doc ic ibuf count =
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

(* Reinitialize the char stream (after a Drop) *)

let reset_input_buffer doc ic ibuf =
  ibuf.str <- Bytes.empty;
  ibuf.len <- 0;
  ibuf.bols <- [];
  ibuf.tokens <- Pcoq.Parsable.make (Stream.from (prompt_char doc ic ibuf));
  ibuf.start <- 0

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
  let (fl,ll) = lines_rec ibuf.len ([],None) ibuf.bols in
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
  let (b,e) = Loc.unloc loc in b-ib.start >= 0 && e-ib.start < ib.len && b<=e
(* Toplevel error explanation. *)
let error_info_for_buffer ?loc phase buf =
  match loc with
  | None -> Topfmt.pr_phase ?loc phase
  | Some loc ->
      let fname = loc.Loc.fname in
        (* We are in the toplevel *)
      match fname with
      | Loc.ToplevelInput ->
        let nloc = adjust_loc_buf buf loc in
        if valid_buffer_loc buf loc then
          match Topfmt.pr_phase ~loc:nloc phase with
          | None -> None
          | Some hd -> Some (hd ++ fnl () ++ print_highlight_location buf nloc)
        (* in the toplevel, but not a valid buffer *)
        else Topfmt.pr_phase ~loc phase
      (* we are in batch mode, don't adjust location *)
      | Loc.InFile _ -> Topfmt.pr_phase ~loc phase

(* Actual printing routine *)
let print_error_for_buffer ?loc phase lvl msg buf =
  let pre_hdr = error_info_for_buffer ?loc phase buf in
  if !print_emacs
  then Topfmt.emacs_logger ?pre_hdr lvl msg
  else Topfmt.std_logger   ?pre_hdr lvl msg

(*
let print_toplevel_parse_error (e, info) buf =
  let loc = Loc.get_loc info in
  let lvl = Feedback.Error in
  let msg = CErrors.iprint (e, info) in
  print_error_for_buffer ?loc lvl msg buf
*)
end

(*s The Coq prompt is the name of the focused proof, if any, and "Coq"
    otherwise. We trap all exceptions to prevent the error message printing
    from cycling. *)
let make_prompt () =
  try
    (Names.Id.to_string (Proof_global.get_current_proof_name ())) ^ " < "
  with Proof_global.NoCurrentProof ->
    "Coq < "

(* the coq prompt added to the default one when in emacs mode
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
  { prompt = pr;
    str = Bytes.empty;
    len = 0;
    bols = [];
    tokens = Pcoq.Parsable.make (Stream.of_list []);
    start = 0 }

let set_prompt prompt =
  top_buffer.prompt
  <- (fun doc ->
    emacs_prompt_startstring()
    ^ prompt ()
    ^ emacs_prompt_endstring())

(* Read the input stream until a dot is encountered *)
let parse_to_dot =
  let rec dot st = match Stream.next st with
    | Tok.KEYWORD ("."|"...") -> ()
    | Tok.EOI -> raise Stm.End_of_input
    | _ -> dot st
  in
  Pcoq.Gram.Entry.of_parser "Coqtoplevel.dot" dot

(* If an error occurred while parsing, we try to read the input until a dot
   token is encountered.
   We assume that when a lexer error occurs, at least one char was eaten *)

let rec discard_to_dot () =
  try
    Pcoq.Entry.parse parse_to_dot top_buffer.tokens
  with
    | Token.Error _ | CLexer.Error.E _ -> discard_to_dot ()
    | Stm.End_of_input -> raise Stm.End_of_input
    | e when CErrors.noncritical e -> ()

let read_sentence ~state input =
  (* XXX: careful with ignoring the state Eugene!*)
  try G_toplevel.parse_toplevel input
  with reraise ->
    let reraise = CErrors.push reraise in
    discard_to_dot ();
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
      Option.cata fst None Stm.(get_ast ~doc sid)
    with _ -> loc

(** Coqloop Console feedback handler *)
let coqloop_feed phase (fb : Feedback.feedback) = let open Feedback in
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
  | Message (Error,loc,msg) -> ()
  (* TopErr.print_error_for_buffer ?loc lvl msg top_buffer *)
  | Message (Warning,loc,msg) ->
    let loc = extract_default_loc loc fb.doc_id fb.span_id in
    TopErr.print_error_for_buffer ?loc phase Warning msg top_buffer
  | Message (lvl,loc,msg) ->
    TopErr.print_error_for_buffer ?loc phase lvl msg top_buffer

(** Main coq loop : read vernacular expressions until Drop is entered.
    Ctrl-C is handled internally as Sys.Break instead of aborting Coq.
    Normally, the only exceptions that can come out of [do_vernac] and
    exit the loop are Drop and Quit. Any other exception there indicates
    an issue with [print_toplevel_error] above. *)

(* Flush in a compatible order with 8.5 *)
(* This mimics the semantics of the old Pp.flush_all *)
let loop_flush_all () =
  Pervasives.flush stderr;
  Pervasives.flush stdout;
  Format.pp_print_flush !Topfmt.std_ft ();
  Format.pp_print_flush !Topfmt.err_ft ()

(* Goal equality heuristic. *)
let pequal cmp1 cmp2 (a1,a2) (b1,b2) = cmp1 a1 b1 && cmp2 a2 b2
let evleq e1 e2 = CList.equal Evar.equal e1 e2
let cproof p1 p2 =
  let (a1,a2,a3,a4,_),(b1,b2,b3,b4,_) = Proof.proof p1, Proof.proof p2 in
  evleq a1 b1 &&
  CList.equal (pequal evleq evleq) a2 b2 &&
  CList.equal Evar.equal a3 b3 &&
  CList.equal Evar.equal a4 b4

let drop_last_doc = ref None

(* todo: could add other Set/Unset commands, such as "Printing Universes" *)
let print_anyway_opts = [
  [ "Diffs" ];
  ]

let print_anyway c =
  let open Vernacexpr in
  match c with
  | VernacExpr (_, VernacSetOption (_, opt, _))
  | VernacExpr (_, VernacUnsetOption (_, opt)) ->
    List.mem opt print_anyway_opts
  | _ -> false

(* We try to behave better when goal printing raises an exception
   [usually Ctrl-C]

   This is mostly a hack as we should protect printing in a more
   generic way, but that'll do for now *)
let top_goal_print ~doc c oldp newp =
  try
    let proof_changed = not (Option.equal cproof oldp newp) in
    let print_goals = proof_changed && Proof_global.there_are_pending_proofs () ||
                      print_anyway c in
    if not !Flags.quiet && print_goals then begin
      let dproof = Stm.get_prev_proof ~doc (Stm.get_current_state ~doc) in
      Printer.print_and_diff dproof newp
    end
  with
  | exn ->
    let (e, info) = CErrors.push exn in
    let loc = Loc.get_loc info in
    let msg = CErrors.iprint (e, info) in
    TopErr.print_error_for_buffer ?loc Topfmt.InteractiveLoop Feedback.Error msg top_buffer

(* Careful to keep this loop tail-rec *)
let rec vernac_loop ~state =
  let open CAst in
  let open Vernac.State in
  let open G_toplevel in
  loop_flush_all ();
  top_stderr (fnl());
  if !print_emacs then top_stderr (str (top_buffer.prompt state.doc));
  resynch_buffer top_buffer;
  (* execute one command *)
  try
    let input = top_buffer.tokens in
    match read_sentence ~state input with
    | {v=VernacBacktrack(bid,_,_)} ->
      let bid = Stateid.of_int bid in
      let doc, res = Stm.edit_at ~doc:state.doc bid in
      assert (res = `NewTip);
      let state = { state with doc; sid = bid } in
      vernac_loop ~state

    | {v=VernacQuit} ->
      exit 0
    | {v=VernacDrop} ->
      if Mltop.is_ocaml_top()
      then (drop_last_doc := Some state; state)
      else (Feedback.msg_warning (str "There is no ML toplevel."); vernac_loop ~state)
    | {v=VernacControl c; loc} ->
      let nstate = Vernac.process_expr ~state (make ?loc c) in
      top_goal_print ~doc:state.doc c state.proof nstate.proof;
      vernac_loop ~state:nstate
  with
  | Stm.End_of_input ->
    top_stderr (fnl ()); exit 0
  (* Exception printing should be done by the feedback listener,
     however this is not yet ready so we rely on the exception for
     now. *)
  | any ->
    let (e, info) = CErrors.push any in
    let loc = Loc.get_loc info in
    let msg = CErrors.iprint (e, info) in
    TopErr.print_error_for_buffer ?loc Topfmt.InteractiveLoop Feedback.Error msg top_buffer;
    vernac_loop ~state

let rec loop ~state =
  let open Vernac.State in
  Sys.catch_break true;
  try
    reset_input_buffer state.doc stdin top_buffer;
    vernac_loop ~state
  with
    | any ->
      top_stderr
        (hov 0 (str "Anomaly: main loop exited with exception:" ++ spc () ++
                str (Printexc.to_string any)) ++ spc () ++
         hov 0 (str "Please report at " ++ str Coq_config.wwwbugtracker ++ str "."));
      loop ~state

(* Default toplevel loop *)
let warning s = Flags.(with_option warn Feedback.msg_warning (strbrk s))

let drop_args = ref None
let loop ~opts ~state =
  drop_args := Some opts;
  let open Coqargs in
  print_emacs := opts.print_emacs;
  (* We initialize the console only if we run the toploop_run *)
  let tl_feed = Feedback.add_feeder (coqloop_feed Topfmt.InteractiveLoop) in
  if Dumpglob.dump () then begin
    Flags.if_verbose warning "Dumpglob cannot be used in interactive mode.";
    Dumpglob.noglob ()
  end;
  let _ = loop ~state in
  (* Initialise and launch the Ocaml toplevel *)
  Coqinit.init_ocaml_path();
  Mltop.ocaml_toploop();
  (* We delete the feeder after the OCaml toploop has ended so users
     of Drop can see the feedback. *)
  Feedback.del_feeder tl_feed
