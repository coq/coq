(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Options
open Cerrors
open Vernac
open Pcoq
open Protectedtoplevel

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

(* Read a char in an input channel, displaying a prompt at every
   beginning of line. *)

let prompt_char ic ibuf count =
  let bol = match ibuf.bols with
    | ll::_ -> ibuf.len == ll
    | [] -> ibuf.len == 0
  in
  if bol then msgerr (str (ibuf.prompt()));
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
  (fl,out_some ll)

let dotted_location (b,e) =
  if e-b < 3 then 
    ("", String.make (e-b) ' ')
  else 
    (String.make (e-b-1) '.', " ")

let print_highlight_location ib (bp,ep) =
  let bp = bp - ib.start 
  and ep = ep - ib.start in
  let highlight_lines =
    match get_bols_of_loc ib (bp,ep) with
      | ([],(bl,el)) ->  
	  (str"> " ++ str(String.sub ib.str bl (el-bl-1)) ++ fnl () ++
             str"> " ++ str(String.make (bp-bl) ' ') ++
             str(String.make (ep-bp) '^'))
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
  (str"Toplevel input, characters " ++ Cerrors.print_loc (bp,ep) ++ fnl () ++
     highlight_lines ++ fnl ())

(* Functions to report located errors in a file. *)

let print_location_in_file s fname (bp,ep) =
  let errstrm = (str"Error while reading " ++ str s ++ str" :" ++ fnl () ++
                   str"File " ++ str ("\""^fname^"\"")) in
  if (bp,ep) = Ast.dummy_loc then 
    (errstrm ++ str", unknown location." ++ fnl ())
  else
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
      (errstrm ++ str", line " ++ int line ++
         str", characters " ++ Cerrors.print_loc (bp-bol,ep-bol) ++ fnl ())
    with e -> (close_in ic; (errstrm ++ str", invalid location." ++ fnl ()))
	
let print_command_location ib dloc =
  match dloc with
    | Some (bp,ep) ->
        (str"Error during interpretation of command:" ++ fnl () ++
           str(String.sub ib.str (bp-ib.start) (ep-bp)) ++ fnl ())
    | None -> (mt ())

let valid_loc dloc (b,e) =
  (b,e) <> Ast.dummy_loc
  & match dloc with
    | Some (bd,ed) -> bd<=b & e<=ed
    | _ -> true
	  
let valid_buffer_loc ib dloc (b,e) =
  valid_loc dloc (b,e) & b-ib.start >= 0 & e-ib.start < ib.len & b<=e 

(*s The Coq prompt is the name of the focused proof, if any, and "Coq"
    otherwise. We trap all exceptions to prevent the error message printing
    from cycling. *)
let make_prompt () =
  try
    (Names.string_of_id (Pfedit.get_current_proof_name ())) ^ " < "
  with _ -> 
    "Coq < "

(* A buffer to store the current command read on stdin. It is
 * initialized when a vernac command is immediately followed by "\n",
 * or after a Drop. *)
let top_buffer =
  let pr() = (make_prompt())^(emacs_str (String.make 1 (Char.chr 249)))
  in
  { prompt = pr;
    str = "";
    len = 0;
    bols = [];
    tokens = Gram.parsable (Stream.of_list []);
    start = 0 }

let set_prompt prompt =
  top_buffer.prompt
  <- (fun () -> (prompt ()) ^ (emacs_str (String.make 1 (Char.chr 249))))

(* Removes and prints the location of the error. The following exceptions
   need not be located. *)
let rec is_pervasive_exn = function
  | Out_of_memory | Stack_overflow | Sys.Break -> true
  | Error_in_file (_,_,e) -> is_pervasive_exn e
  | Stdpp.Exc_located (_,e) -> is_pervasive_exn e
  | DuringCommandInterp (_,e) -> is_pervasive_exn e
  | _ -> false

(* Toplevel error explanation, dealing with locations, Drop, Ctrl-D
   May raise only the following exceptions: Drop and End_of_input,
   meaning we get out of the Coq loop *)
let print_toplevel_error exc =
  let (dloc,exc) =
    match exc with
      | DuringCommandInterp (loc,ie) ->
          if loc = Ast.dummy_loc then (None,ie) else (Some loc, ie)
      | _ -> (None, exc) 
  in
  let (locstrm,exc) =
    match exc with
      | Stdpp.Exc_located (loc, ie) ->
          if valid_buffer_loc top_buffer dloc loc then
            (print_highlight_location top_buffer loc, ie)
          else 
	    ((mt ()) (* print_command_location top_buffer dloc *), ie)
      | Error_in_file (s, (fname, loc), ie) ->
          (print_location_in_file s fname loc, ie)
      | _ -> 
	  ((mt ()) (* print_command_location top_buffer dloc *), exc)
  in
  match exc with
    | End_of_input -> 
	msgerrnl (mt ()); pp_flush(); exit 0
    | Vernacexpr.Drop ->  (* Last chance *)
        if Mltop.is_ocaml_top() then raise Vernacexpr.Drop;
        (str"Error: There is no ML toplevel." ++ fnl ())
    | Vernacexpr.ProtectedLoop ->
	raise Vernacexpr.ProtectedLoop
    | Vernacexpr.Quit -> 
	raise Vernacexpr.Quit
    | _ -> 
	(if is_pervasive_exn exc then (mt ()) else locstrm) ++
        Cerrors.explain_exn exc

(* Read the input stream until a dot is encountered *)
let parse_to_dot =
  let rec dot st = match Stream.next st with
    | ("", ".") -> ()
    | ("EOI", "") -> raise End_of_input
    | _ -> dot st
  in 
  Gram.Entry.of_parser "Coqtoplevel.dot" dot
    
(* We assume that when a lexer error occurs, at least one char was eaten *)
let rec discard_to_dot () =
  try 
    Gram.Entry.parse parse_to_dot top_buffer.tokens
  with Stdpp.Exc_located(_,Token.Error _) -> 
    discard_to_dot()


(* If the error occured while parsing, we read the input until a dot token
 * in encountered. *)

let process_error = function
  | DuringCommandInterp _ as e -> e
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
 * The boolean value is used to choose between a protected loop, which
 * we think is more suited for communication with other programs, or
 * plain communication. *)

let rec coq_switch b =
  Sys.catch_break true;
  (* ensure we have a command separator object (DOT) so that the first
     command can be reseted. *)
  Lib.mark_end_of_command();
  try
    if b then begin
      reset_input_buffer stdin top_buffer;
      while true do do_vernac() done
    end else
      protected_loop stdin
  with
    | Vernacexpr.Drop -> ()
    | Vernacexpr.ProtectedLoop -> 
	Lib.declare_initial_state();
	coq_switch false
    | End_of_input -> msgerrnl (mt ()); pp_flush(); exit 0
    | Vernacexpr.Quit -> exit 0
    | e ->
	msgerrnl (str"Anomaly: toplevel loop. Please report.");
	coq_switch b

let loop () = coq_switch true
