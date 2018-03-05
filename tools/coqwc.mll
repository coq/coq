(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* coqwc - counts the lines of spec, proof and comments in Coq sources
 * Copyright (C) 2003 Jean-Christophe Filliâtre *)

(*s {\bf coqwc.} Counts the lines of spec, proof and comments in a Coq source.
    It assumes the files to be lexically well-formed. *)

(*i*){
open Printf
open Lexing
(*i*)

(*s Command-line options. *)

let spec_only = ref false
let proof_only = ref false
let percentage = ref false
let skip_header = ref true

(*s Counters. [clines] counts the number of code lines of the current
    file, and [dlines] the number of comment lines. [tclines] and [tdlines]
    are the corresponding totals. *)

let slines = ref 0
let plines = ref 0
let dlines = ref 0

let tslines = ref 0
let tplines = ref 0
let tdlines = ref 0

let update_totals () =
  tslines := !tslines + !slines;
  tplines := !tplines + !plines;
  tdlines := !tdlines + !dlines

(*s The following booleans indicate whether we have seen spec, proof or
    comment so far on the current line; when a newline is reached, [newline]
    is called and updates the counters accordingly. *)

let seen_spec = ref false
let seen_proof = ref false
let seen_comment = ref false

let newline () =
  if !seen_spec then incr slines;
  if !seen_proof then incr plines;
  if !seen_comment then incr dlines;
  seen_spec := false; seen_proof := false; seen_comment := false

let reset_counters () =
  seen_spec := false; seen_proof := false; seen_comment := false;
  slines := 0; plines := 0; dlines := 0

(*s Print results. *)

let print_line sl pl dl fo =
  if not !proof_only then printf " %8d" sl;
  if not !spec_only then printf " %8d" pl;
  if not (!proof_only || !spec_only) then printf " %8d" dl;
  (match fo with Some f -> printf " %s" f | _ -> ());
  if !percentage then begin
    let s = sl + pl + dl in
    let p = if s > 0 then 100 * dl / s else 0 in
    printf " (%d%%)" p
  end;
  print_newline ()

let print_file fo = print_line !slines !plines !dlines fo

let print_totals () = print_line !tslines !tplines !tdlines (Some "total")

(*i*)}(*i*)

(*s Shortcuts for regular expressions. The [rcs] regular expression
    is used to skip the CVS infos possibly contained in some comments,
    in order not to consider it as documentation. *)

let space = [' ' '\t' '\r']
let character =
  "'" ([^ '\\' '\''] |
       '\\' (['\\' '\'' 'n' 't' 'b' 'r'] | ['0'-'9'] ['0'-'9'] ['0'-'9'])) "'"
let rcs_keyword =
  "Author" | "Date" | "Header" | "Id" | "Name" | "Locker" | "Log" |
  "RCSfile" | "Revision" | "Source" | "State"
let rcs = "\036" rcs_keyword [^ '$']* "\036"
let stars = "(*" '*'* "*)"
let dot = '.' (' ' | '\t' | '\n' | '\r' | eof)
let proof_start =
  "Theorem" | "Lemma" | "Fact" | "Remark" | "Goal" | "Correctness" | "Obligation" space+ (['0' - '9'])+ | "Next" space+ "Obligation"
let def_start =
  "Definition" | "Fixpoint" | "Instance"
let proof_end =
  ("Save" | "Qed" | "Defined" | "Abort" | "Admitted") [^'.']* '.'

(*s [spec] scans the specification. *)

rule spec = parse
  | "(*"   { comment lexbuf; spec lexbuf }
  | '"'    { let n = string lexbuf in slines := !slines + n;
	     seen_spec := true; spec lexbuf }
  | '\n'   { newline (); spec lexbuf }
  | space+ | stars
           { spec lexbuf }
  | proof_start
           { seen_spec := true; spec_to_dot lexbuf; proof lexbuf }
  | def_start
           { seen_spec := true; definition lexbuf }
  | character | _
	   { seen_spec := true; spec lexbuf }
  | eof    { () }

(*s [spec_to_dot] scans a spec until a dot is reached and returns. *)

and spec_to_dot = parse
  | "(*"   { comment lexbuf; spec_to_dot lexbuf }
  | '"'    { let n = string lexbuf in slines := !slines + n;
	     seen_spec := true; spec_to_dot lexbuf }
  | '\n'   { newline (); spec_to_dot lexbuf }
  | dot    { () }
  | space+ | stars
           { spec_to_dot lexbuf }
  | character | _
	   { seen_spec := true; spec_to_dot lexbuf }
  | eof    { () }

(*s [definition] scans a definition; passes to [proof] if the body is
    absent, and to [spec] otherwise *)

and definition = parse
  | "(*"   { comment lexbuf; definition lexbuf }
  | '"'    { let n = string lexbuf in slines := !slines + n;
	     seen_spec := true; definition lexbuf }
  | '\n'   { newline (); definition lexbuf }
  | ":="   { seen_spec := true; spec lexbuf }
  | dot    { proof lexbuf }
  | space+ | stars
           { definition lexbuf }
  | character | _
	   { seen_spec := true; definition lexbuf }
  | eof    { () }

(*s Scans a proof, then returns to [spec]. *)

and proof = parse
  | "(*"   { comment lexbuf; proof lexbuf }
  | '"'    { let n = string lexbuf in plines := !plines + n;
	     seen_proof := true; proof lexbuf }
  | space+ | stars
           { proof lexbuf }
  | '\n'   { newline (); proof lexbuf }
  | "Proof" space* '.'
  | "Proof" space+ "with"
  | "Proof" space+ "using"
           { seen_proof := true; proof lexbuf }
  | "Proof" space
           { proof_term lexbuf }
  | proof_end
           { seen_proof := true; spec lexbuf }
  | character | _
	   { seen_proof := true; proof lexbuf }
  | eof    { () }

and proof_term = parse
  | "(*"   { comment lexbuf; proof_term lexbuf }
  | '"'    { let n = string lexbuf in plines := !plines + n;
	     seen_proof := true; proof_term lexbuf }
  | space+ | stars
           { proof_term lexbuf }
  | '\n'   { newline (); proof_term lexbuf }
  | dot    { spec lexbuf }
  | character | _
	   { seen_proof := true; proof_term lexbuf }
  | eof    { () }

(*s Scans a comment. *)

and comment = parse
  | "(*"   { comment lexbuf; comment lexbuf }
  | "*)"   { () }
  | '"'    { let n = string lexbuf in dlines := !dlines + n;
	     seen_comment := true; comment lexbuf }
  | '\n'   { newline (); comment lexbuf }
  | space+ | stars
	   { comment lexbuf }
  | character | _
	   { seen_comment := true; comment lexbuf }
  | eof    { () }

(*s The entry [string] reads a string until its end and returns the number
    of newlines it contains. *)

and string = parse
  | '"'  { 0 }
  | '\\' ('\\' | 'n' | '"') { string lexbuf }
  | '\n' { succ (string lexbuf) }
  | _    { string lexbuf }
  | eof  { 0 }

(*s The following entry [read_header] is used to skip the possible header at
    the beggining of files (unless option \texttt{-e} is specified).
    It stops whenever it encounters an empty line or any character outside
    a comment. In this last case, it correctly resets the lexer position
    on that character (decreasing [lex_curr_pos] by 1). *)

and read_header = parse
  | "(*"   { skip_comment lexbuf; skip_until_nl lexbuf;
	     read_header lexbuf }
  | "\n"   { () }
  | space+ { read_header lexbuf }
  | _      { lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos - 1 }
  | eof    { () }

and skip_comment = parse
  | "*)" { () }
  | "(*" { skip_comment lexbuf; skip_comment lexbuf }
  | _    { skip_comment lexbuf }
  | eof  { () }

and skip_until_nl = parse
  | '\n' { () }
  | _    { skip_until_nl lexbuf }
  | eof  { () }

(*i*){(*i*)

(*s Processing files and channels. *)

let process_channel ch =
  let lb = Lexing.from_channel ch in
  reset_counters ();
  if !skip_header then read_header lb;
  spec lb

[@@@ocaml.warning "-52"]
let process_file f =
  try
    let ch = open_in f in
    process_channel ch;
    close_in ch;
    print_file (Some f);
    update_totals ()
  with
    | Sys_error "Is a directory" ->
	flush stdout; eprintf "coqwc: %s: Is a directory\n" f; flush stderr
    | Sys_error s ->
	flush stdout; eprintf "coqwc: %s\n" s; flush stderr
[@@@ocaml.warning "+52"]

(*s Parsing of the command line. *)

let usage () =
  prerr_endline "usage: coqwc [options] [files]";
  prerr_endline "Options are:";
  prerr_endline "  -p   print percentage of comments";
  prerr_endline "  -s   print only the spec size";
  prerr_endline "  -r   print only the proof size";
  prerr_endline "  -e   (everything) do not skip headers";
  exit 1

let rec parse = function
  | [] -> []
  | ("-h" | "-?" | "-help" | "--help") :: _ -> usage ()
  | ("-s" | "--spec-only") :: args ->
      proof_only := false; spec_only := true; parse args
  | ("-r" | "--proof-only") :: args ->
      spec_only := false; proof_only := true; parse args
  | ("-p" | "--percentage") :: args -> percentage := true; parse args
  | ("-e" | "--header") :: args -> skip_header := false; parse args
  | f :: args -> f :: (parse args)

(*s Main program. *)

let _ =
  let files = parse (List.tl (Array.to_list Sys.argv)) in
  if not (!spec_only || !proof_only) then
    printf "     spec    proof comments\n";
  match files with
    | [] -> process_channel stdin; print_file None
    | [f] -> process_file f
    | _ -> List.iter process_file files; print_totals ()

(*i*)}(*i*)


