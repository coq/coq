(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Flags
open Vernac
open Pcoq

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


(* emacs special prompt tag for easy detection. No special character,
   to avoid interfering with utf8. Compatibility code removed. *)

let emacs_prompt_startstring() = Printer.emacs_str "<prompt>"

let emacs_prompt_endstring() = Printer.emacs_str "</prompt>"

(* Read a char in an input channel, displaying a prompt at every
   beginning of line. *)
let prompt_char ic ibuf count =
  let bol = match ibuf.bols with
    | ll::_ -> Int.equal ibuf.len ll
    | [] -> Int.equal ibuf.len 0
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
    if b < 0 || e < b then anomaly (Pp.str "Bad location");
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
    if s.[i] == '\t' then s'.[!j] <- '\t';
    if n < 0x80 || 0xC0 <= n then incr j
  done;
  String.sub s' 0 !j

let print_highlight_location ib loc =
  let (bp,ep) = Loc.unloc loc in
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
  let loc = Loc.make_loc (bp,ep) in
  (str"Toplevel input, characters " ++ Cerrors.print_loc loc ++ str":" ++ fnl () ++
     highlight_lines ++ fnl ())

(* Functions to report located errors in a file. *)

let print_location_in_file {outer=s;inner=fname} loc =
  let errstrm = str"Error while reading " ++ str s in
  if Loc.is_ghost loc then
    hov 1 (errstrm ++ spc() ++ str" (unknown location):") ++ fnl ()
  else
    let errstrm =
      if String.equal s fname then mt() else errstrm ++ str":" ++ fnl()
    in
    let (bp,ep) = Loc.unloc loc in
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
           Cerrors.print_loc (Loc.make_loc (bp-bol,ep-bol))) ++ str":" ++
        fnl ()
    with e when Errors.noncritical e ->
      (close_in ic;
       hov 1 (errstrm ++ spc() ++ str"(invalid location):") ++ fnl ())

let valid_buffer_loc ib loc =
  not (Loc.is_ghost loc) &&
  let (b,e) = Loc.unloc loc in b-ib.start >= 0 && e-ib.start < ib.len && b<=e

(*s The Coq prompt is the name of the focused proof, if any, and "Coq"
    otherwise. We trap all exceptions to prevent the error message printing
    from cycling. *)
let make_prompt () =
  try
    (Names.Id.to_string (Pfedit.get_current_proof_name ())) ^ " < "
  with Proof_global.NoCurrentProof ->
    "Coq < "

(*let build_pending_list l =
  let pl = ref ">" in
  let l' = ref l in
  let res =
    while List.length !l' > 1 do
      pl := !pl ^ "|" Names.Id.to_string x;
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
  let statnum = Stateid.to_string (Stm.get_current_state ()) in
  let dpth = Stm.current_proof_depth() in
  let pending = Stm.get_all_proof_names() in
  let pendingprompt =
    List.fold_left
      (fun acc x -> acc ^ (if String.is_empty acc then "" else "|") ^ Names.Id.to_string x)
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

(* The following exceptions need not be located. *)

let locate_exn = function
  | Out_of_memory | Stack_overflow | Sys.Break -> false
  | _ -> true

(* Toplevel error explanation. *)

let print_toplevel_error e =
  let loc = Option.default Loc.ghost (Loc.get_loc e) in
  let locmsg = match Vernac.get_exn_files e with
    | Some files -> print_location_in_file files loc
    | None ->
      if locate_exn e && valid_buffer_loc top_buffer loc then
        print_highlight_location top_buffer loc
      else mt ()
  in
  locmsg ++ Errors.print e

(* Read the input stream until a dot is encountered *)
let parse_to_dot =
  let rec dot st = match Compat.get_tok (Stream.next st) with
    | Tok.KEYWORD "." -> ()
    | Tok.EOI -> raise End_of_input
    | _ -> dot st
  in
  Gram.Entry.of_parser "Coqtoplevel.dot" dot

(* If an error occured while parsing, we try to read the input until a dot
   token is encountered.
   We assume that when a lexer error occurs, at least one char was eaten *)

let rec discard_to_dot () =
  try
    Gram.entry_parse parse_to_dot top_buffer.tokens
  with
    | Compat.Token.Error _ | Lexer.Error.E _ -> discard_to_dot ()
    | End_of_input -> raise End_of_input
    | e when Errors.noncritical e -> ()

let read_sentence () =
  try Vernac.parse_sentence (top_buffer.tokens, None)
  with reraise ->
    let reraise = Errors.push reraise in
    discard_to_dot ();
    raise reraise

(** [do_vernac] reads and executes a toplevel phrase, and print error
    messages when an exception is raised, except for the following:
    - Drop: kill the Coq toplevel, going down to the Caml toplevel if it exists.
           Otherwise, exit.
    - End_of_input: Ctrl-D was typed in, we will quit.

    In particular, this is normally the only place where a Sys.Break
    is catched and handled (i.e. not re-raised).
*)

let do_vernac () =
  msgerrnl (mt ());
  if !print_emacs then msgerr (str (top_buffer.prompt()));
  resynch_buffer top_buffer;
  try
    Vernac.eval_expr (read_sentence ())
  with
    | End_of_input | Errors.Quit ->
        msgerrnl (mt ()); pp_flush(); raise Errors.Quit
    | Errors.Drop ->  (* Last chance *)
        if Mltop.is_ocaml_top() then raise Errors.Drop
        else ppnl (str"Error: There is no ML toplevel." ++ fnl ())
    | any ->
        Format.set_formatter_out_channel stdout;
        ppnl (print_toplevel_error any);
        pp_flush ()

(** Main coq loop : read vernacular expressions until Drop is entered.
    Ctrl-C is handled internally as Sys.Break instead of aborting Coq.
    Normally, the only exceptions that can come out of [do_vernac] and
    exit the loop are Drop and Quit. Any other exception there indicates
    an issue with [print_toplevel_error] above. *)

(*
let feed_emacs = function
  | { Interface.id = Interface.State id;
      Interface.content = Interface.GlobRef (_,a,_,c,_) }  -> 
    prerr_endline ("<info>" ^"<id>"^Stateid.to_string id ^"</id>"
		   ^a^" "^c^ "</info>")
  | _  -> ()
*)

let rec loop () =
  Sys.catch_break true;
  if !Flags.print_emacs then begin
    (* TODO : check with Enrico ?! *)
    (*
    Pp.set_feeder feed_emacs;
    Vernacentries.enable_goal_printing := false;
    *)
    Vernacentries.qed_display_script := false;
  end;
  try
    reset_input_buffer stdin top_buffer;
    while true do do_vernac(); flush_all() done
  with
    | Errors.Drop -> ()
    | Errors.Quit -> exit 0
    | any ->
      msgerrnl (str"Anomaly: main loop exited with exception: " ++
                str (Printexc.to_string any) ++
                fnl() ++ str"Please report.");
      loop ()
