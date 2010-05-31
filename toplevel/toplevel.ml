(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Flags
open Cerrors
open Vernac
open Vernacexpr
open Pcoq
open Compat

(* A buffer for the character read from a channel. We store the command
 * entered to be able to report errors without pretty-printing. *)

type input_buffer = {
  mutable prompt : unit -> string;
  mutable str : string; (* buffer of already read characters *)
  mutable len : int;    (* number of chars in the buffer *)
  mutable bols : int list; (* offsets in str of begining of lines *)
  mutable tokens : Gram.parsable; (* stream of tokens *)
  mutable start : int } (* stream count of the first char of the buffer *)

(* Double the size of the buffer. *)

let resize_buffer ibuf =
  let nstr = String.create (2 * String.length ibuf.str + 1) in
  String.blit ibuf.str 0 nstr 0 (String.length ibuf.str);
  ibuf.str <- nstr

(* Delete all irrelevent lines of the input buffer. Keep the last line
   in the buffer (useful when there are several commands on the same line. *)

let resynch_buffer ibuf =
  match ibuf.bols with
    | ll::_ ->
        let new_len = ibuf.len - ll in
        String.blit ibuf.str ll ibuf.str 0 new_len;
        ibuf.len <- new_len;
        ibuf.bols <- [];
        ibuf.start <- ibuf.start + ll
    | _ -> ()


(* emacs special character for prompt end (fast) detection. Prefer
   (Char.chr 6) since it does not interfere with utf8. For
    compatibility we let (Char.chr 249) as default for a while. *)

let emacs_prompt_startstring() = Printer.emacs_str "" "<prompt>"

let emacs_prompt_endstring() = Printer.emacs_str (String.make 1 (Char.chr 249)) "</prompt>"

(* Read a char in an input channel, displaying a prompt at every
   beginning of line. *)
let prompt_char ic ibuf count =
  let bol = match ibuf.bols with
    | ll::_ -> ibuf.len == ll
    | [] -> ibuf.len == 0
  in
  if bol && not !print_emacs then msgerr (str (ibuf.prompt()));
  try
    let c = input_char ic in
    if c == '\n' then ibuf.bols <- (ibuf.len+1) :: ibuf.bols;
    if ibuf.len == String.length ibuf.str then resize_buffer ibuf;
    ibuf.str.[ibuf.len] <- c;
    ibuf.len <- ibuf.len + 1;
    Some c
  with End_of_file ->
    None

(* Reinitialize the char stream (after a Drop) *)

let reset_input_buffer ic ibuf =
  ibuf.str <- "";
  ibuf.len <- 0;
  ibuf.bols <- [];
  ibuf.tokens <- Gram.parsable (Stream.from (prompt_char ic ibuf));
  ibuf.start <- 0

(* Functions to print underlined locations from an input buffer. *)

(* Given a location, returns the list of locations of each line. The last
   line is returned separately. It also checks the location bounds. *)

let get_bols_of_loc ibuf (bp,ep) =
  let add_line (b,e) lines =
    if b < 0 or e < b then anomaly "Bad location";
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

let blanch_utf8_string s bp ep =
  let s' = String.make (ep-bp) ' ' in
  let j = ref 0 in
  for i = bp to ep - 1 do
    let n = Char.code s.[i] in
    (* Heuristic: assume utf-8 chars are printed using a single
    fixed-size char and therefore contract all utf-8 code into one
    space; in any case, preserve tabulation so
    that its effective interpretation in terms of spacing is preserved *)
    if s.[i] = '\t' then s'.[!j] <- '\t';
    if n < 0x80 || 0xC0 <= n then incr j
  done;
  String.sub s' 0 !j

let print_highlight_location ib loc =
  let (bp,ep) = unloc loc in
  let bp = bp - ib.start
  and ep = ep - ib.start in
  let highlight_lines =
    match get_bols_of_loc ib (bp,ep) with
      | ([],(bl,el)) ->
	  let shift = blanch_utf8_string ib.str bl bp in
	  let span = String.length (blanch_utf8_string ib.str bp ep) in
	  (str"> " ++ str(String.sub ib.str bl (el-bl-1)) ++ fnl () ++
           str"> " ++ str(shift) ++ str(String.make span '^'))
      | ((b1,e1)::ml,(bn,en)) ->
          let (d1,s1) = dotted_location (b1,bp) in
          let (dn,sn) = dotted_location (ep,en) in
          let l1 = (str"> " ++ str d1 ++ str s1 ++
                      str(String.sub ib.str bp (e1-bp))) in
          let li =
            prlist (fun (bi,ei) ->
                      (str"> " ++ str(String.sub ib.str bi (ei-bi)))) ml in
          let ln = (str"> " ++ str(String.sub ib.str bn (ep-bn)) ++
                      str sn ++ str dn) in
	  (l1 ++ li ++ ln)
  in
  let loc = make_loc (bp,ep) in
  (str"Toplevel input, characters " ++ Cerrors.print_loc loc ++ str":" ++ fnl () ++
     highlight_lines ++ fnl ())

(* Functions to report located errors in a file. *)

let print_location_in_file s inlibrary fname loc =
  let errstrm = str"Error while reading " ++ str s in
  if loc = dummy_loc then
    hov 1 (errstrm ++ spc() ++ str" (unknown location):") ++ fnl ()
  else
    let errstrm =
      if s = fname then mt() else errstrm ++ str":" ++ fnl() in
    if inlibrary then
      hov 0 (errstrm ++ str"Module " ++ str ("\""^fname^"\"") ++ spc() ++
             str"characters " ++ Cerrors.print_loc loc) ++ fnl ()
    else
      let (bp,ep) = unloc loc in
      let ic = open_in fname in
      let rec line_of_pos lin bol cnt =
        if cnt < bp then
          if input_char ic == '\n'
          then line_of_pos (lin + 1) (cnt +1) (cnt+1)
          else line_of_pos lin bol (cnt+1)
        else (lin, bol)
      in
      try
        let (line, bol) = line_of_pos 1 0 0 in
        close_in ic;
        hov 0 (* No line break so as to follow emacs error message format *)
          (errstrm ++ str"File " ++ str ("\""^fname^"\"") ++
           str", line " ++ int line ++ str", characters " ++
           Cerrors.print_loc (make_loc (bp-bol,ep-bol))) ++ str":" ++
        fnl ()
      with e ->
        (close_in ic;
         hov 1 (errstrm ++ spc() ++ str"(invalid location):") ++ fnl ())

let print_command_location ib dloc =
  match dloc with
    | Some (bp,ep) ->
        (str"Error during interpretation of command:" ++ fnl () ++
           str(String.sub ib.str (bp-ib.start) (ep-bp)) ++ fnl ())
    | None -> (mt ())

let valid_loc dloc loc =
  loc <> dummy_loc
  & match dloc with
    | Some dloc ->
	let (bd,ed) = unloc dloc in let (b,e) = unloc loc in bd<=b & e<=ed
    | _ -> true

let valid_buffer_loc ib dloc loc =
  valid_loc dloc loc &
  let (b,e) = unloc loc in b-ib.start >= 0 & e-ib.start < ib.len & b<=e

(*s The Coq prompt is the name of the focused proof, if any, and "Coq"
    otherwise. We trap all exceptions to prevent the error message printing
    from cycling. *)
let make_prompt () =
  try
    (Names.string_of_id (Pfedit.get_current_proof_name ())) ^ " < "
  with _ ->
    "Coq < "

(*let build_pending_list l =
  let pl = ref ">" in
  let l' = ref l in
  let res =
    while List.length !l' > 1 do
      pl := !pl ^ "|" Names.string_of_id x;
      l':=List.tl !l'
    done in
  let last = try List.hd !l' with _ ->   in
  "<"^l'
*)

(* the coq prompt added to the default one when in emacs mode
   The prompt contains the current state label [n] (for global
   backtracking) and the current proof state [p] (for proof
   backtracking) plus the list of open (nested) proofs (for proof
   aborting when backtracking). It looks like:

   "n |lem1|lem2|lem3| p < "
*)
let make_emacs_prompt() =
  let statnum = string_of_int (Lib.current_command_label ()) in
  let dpth = Pfedit.current_proof_depth() in
  let pending = Pfedit.get_all_proof_names() in
  let pendingprompt =
    List.fold_left
      (fun acc x -> acc ^ (if acc <> "" then "|" else "") ^ Names.string_of_id x)
      "" pending in
  let proof_info = if dpth >= 0 then string_of_int dpth else "0" in
  if !Flags.print_emacs then statnum ^ " |" ^ pendingprompt ^ "| " ^ proof_info ^ " < "
  else ""

(* A buffer to store the current command read on stdin. It is
 * initialized when a vernac command is immediately followed by "\n",
 * or after a Drop. *)
let top_buffer =
  let pr() =
    emacs_prompt_startstring()
    ^ make_prompt()
    ^ make_emacs_prompt()
    ^ emacs_prompt_endstring()
  in
  { prompt = pr;
    str = "";
    len = 0;
    bols = [];
    tokens = Gram.parsable (Stream.of_list []);
    start = 0 }

let set_prompt prompt =
  top_buffer.prompt
  <- (fun () ->
    emacs_prompt_startstring()
    ^ prompt ()
    ^ emacs_prompt_endstring())

(* Removes and prints the location of the error. The following exceptions
   need not be located. *)
let rec is_pervasive_exn = function
  | Out_of_memory | Stack_overflow | Sys.Break -> true
  | Error_in_file (_,_,e) -> is_pervasive_exn e
  | Loc.Exc_located (_,e) -> is_pervasive_exn e
  | DuringCommandInterp (_,e) -> is_pervasive_exn e
  | DuringSyntaxChecking (_,e) -> is_pervasive_exn e
  | _ -> false

(* Toplevel error explanation, dealing with locations, Drop, Ctrl-D
   May raise only the following exceptions: Drop and End_of_input,
   meaning we get out of the Coq loop *)
let print_toplevel_error exc =
  let (dloc,exc) =
    match exc with
      | DuringCommandInterp (loc,ie)
      | DuringSyntaxChecking (loc,ie) ->
          if loc = dummy_loc then (None,ie) else (Some loc, ie)
      | _ -> (None, exc)
  in
  let (locstrm,exc) =
    match exc with
      | Loc.Exc_located (loc, ie) ->
          if valid_buffer_loc top_buffer dloc loc then
            (print_highlight_location top_buffer loc, ie)
          else
	    ((mt ()) (* print_command_location top_buffer dloc *), ie)
      | Error_in_file (s, (inlibrary, fname, loc), ie) ->
          (print_location_in_file s inlibrary fname loc, ie)
      | _ ->
	  ((mt ()) (* print_command_location top_buffer dloc *), exc)
  in
  match exc with
    | End_of_input ->
	msgerrnl (mt ()); pp_flush(); exit 0
    | Vernacexpr.Drop ->  (* Last chance *)
        if Mltop.is_ocaml_top() then raise Vernacexpr.Drop;
        (str"Error: There is no ML toplevel." ++ fnl ())
    | Vernacexpr.Quit ->
	raise Vernacexpr.Quit
    | _ ->
	(if is_pervasive_exn exc then (mt ()) else locstrm) ++
        Cerrors.explain_exn exc

(* Read the input stream until a dot is encountered *)
let parse_to_dot =
  let rec dot st = match get_tok (Stream.next st) with
    | Tok.KEYWORD "." -> ()
    | Tok.EOI -> raise End_of_input
    | _ -> dot st
  in
  Gram.Entry.of_parser "Coqtoplevel.dot" dot

(* We assume that when a lexer error occurs, at least one char was eaten *)
let rec discard_to_dot () =
  try
    Gram.entry_parse parse_to_dot top_buffer.tokens
  with Loc.Exc_located(_,(Token.Error _|Lexer.Error.E _)) ->
    discard_to_dot()


(* If the error occured while parsing, we read the input until a dot token
 * in encountered. *)

let process_error = function
  | DuringCommandInterp _
  | DuringSyntaxChecking _ as e -> e
  | e ->
      if is_pervasive_exn e then
	e
      else
        try
	  discard_to_dot (); e
	with
          | End_of_input -> End_of_input
          | de -> if is_pervasive_exn de then de else e

(* do_vernac reads and executes a toplevel phrase, and print error
   messages when an exception is raised, except for the following:
     Drop: kill the Coq toplevel, going down to the Caml toplevel if it exists.
           Otherwise, exit.
     End_of_input: Ctrl-D was typed in, we will quit *)
let do_vernac () =
  msgerrnl (mt ());
  if !print_emacs then msgerr (str (top_buffer.prompt()));
  resynch_buffer top_buffer;
  begin
    try
      raw_do_vernac top_buffer.tokens
    with e ->
      msgnl (print_toplevel_error (process_error e))
  end;
  flush_all()

(* coq and go read vernacular expressions until Drop is entered.
 * Ctrl-C will raise the exception Break instead of aborting Coq.
 * Here we catch the exceptions terminating the Coq loop, and decide
 * if we really must quit.
 *)

let rec loop () =
  Sys.catch_break true;
  (* ensure we have a command separator object (DOT) so that the first
     command can be reseted. *)
  Lib.mark_end_of_command();
  try
    reset_input_buffer stdin top_buffer;
    while true do do_vernac() done
  with
    | Vernacexpr.Drop -> ()
    | End_of_input -> msgerrnl (mt ()); pp_flush(); exit 0
    | Vernacexpr.Quit -> exit 0
    | e ->
	msgerrnl (str"Anomaly. Please report.");
	loop ()
