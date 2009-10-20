(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

{

  open Lexing

  type color = GText.tag

  type highlight_order = int * int * color

  let comment_start = ref 0

  (* Without this table, the automaton would be too big and
     ocamllex would fail *)
  let is_one_word_command =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [  "Add" ; "Check"; "Eval"; "Extraction" ;
	 "Load" ; "Undo"; "Goal";
	 "Proof" ; "Print"; "Qed" ; "Defined" ; "Save" ;
	 "End" ; "Section"; "Chapter"; "Transparent"; "Opaque"; "Comments"
      ];
    Hashtbl.mem h

  let is_constr_kw =
    let h = Hashtbl.create 97 in
      List.iter (fun s -> Hashtbl.add h s ())
	[ "forall"; "fun"; "match"; "fix"; "cofix"; "with"; "for";
	  "end"; "as"; "let"; "in"; "dest"; "if"; "then"; "else"; "return";
	  "Prop"; "Set"; "Type" ];
      Hashtbl.mem h

  (* Without this table, the automaton would be too big and
     ocamllex would fail *)
  let is_one_word_declaration =
    let h = Hashtbl.create 97 in
      List.iter (fun s -> Hashtbl.add h s ())
	[ (* Theorems *)
          "Theorem" ; "Lemma" ; "Fact" ; "Remark" ; "Corollary" ;
	  "Proposition" ; "Property" ;
          (* Definitions *)
	  "Definition" ; "Let" ; "Example" ; "SubClass" ;
          "Fixpoint" ; "CoFixpoint" ; "Scheme" ; "Function" ;
          (* Assumptions *)
	  "Hypothesis" ; "Variable" ; "Axiom" ; "Parameter" ; "Conjecture" ;
	  "Hypotheses" ; "Variables" ; "Axioms" ; "Parameters";
          (* Inductive *)
          "Inductive" ; "CoInductive" ; "Record" ; "Structure" ;
          (* Other *)
	  "Ltac" ; "Typeclasses"; "Instance"; "Include"; "Context"; "Class"
	];
      Hashtbl.mem h

  let starting = ref true
}

let space =
  [' ' '\010' '\013' '\009' '\012']
let firstchar =
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let identchar =
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let ident = firstchar identchar*

let multiword_declaration =
  "Module" (space+ "Type")?
| "Program" space+ ident
| "Existing" space+ "Instance"
| "Canonical" space+ "Structure"

let locality = ("Local" space+)?

let multiword_command =
  "Set" (space+ ident)*
| "Unset" (space+ ident)*
| "Open" space+ locality "Scope"
| "Close" space+ locality "Scope"
| "Bind" space+ "Scope"
| "Arguments" space+ "Scope"
| "Reserved" space+ "Notation" space+ locality
| "Delimit" space+ "Scope"
| "Next" space+ "Obligation"
| "Solve" space+ "Obligations"
| "Require" space+ ("Import"|"Export")?
| "Infix" space+ locality
| "Notation" space+ locality
| "Hint" space+ locality ident
| "Reset" (space+ "Initial")?
| "Tactic" space+ "Notation"
| "Implicit" space+ "Arguments"
| "Implicit" space+ ("Type"|"Types")
| "Combined" space+ "Scheme"

(* At least still missing: "Inline" + decl, variants of "Identity
  Coercion", variants of Print, Add, ... *)

rule next_starting_order = parse
  | "(*" { comment_start := lexeme_start lexbuf; comment lexbuf }
  | space+ { next_starting_order lexbuf }
  | multiword_declaration
      { starting:=false; lexeme_start lexbuf, lexeme_end lexbuf, Tags.Script.decl }
  | multiword_command
      { starting:=false; lexeme_start lexbuf, lexeme_end lexbuf, Tags.Script.kwd }
  | ident as id
      { if id = "Time" then next_starting_order lexbuf else
	begin
	  starting:=false;
          if is_one_word_command id then
	    lexeme_start lexbuf, lexeme_end lexbuf, Tags.Script.kwd
	  else if is_one_word_declaration id then
	    lexeme_start lexbuf, lexeme_end lexbuf, Tags.Script.decl
	  else
	    next_interior_order lexbuf
	end
      }
  | _    { starting := false; next_interior_order lexbuf}
  | eof  { raise End_of_file }

and next_interior_order = parse
  | "(*"
      { comment_start := lexeme_start lexbuf; comment lexbuf }
  | ident as id
      { if is_constr_kw id then
	  lexeme_start lexbuf, lexeme_end lexbuf, Tags.Script.kwd
        else
	  next_interior_order lexbuf }
  | "." (" "|"\n"|"\t") { starting := true; next_starting_order lexbuf }
  | _    { next_interior_order lexbuf}
  | eof  { raise End_of_file }

and comment = parse
  | "*)" { !comment_start,lexeme_end lexbuf,Tags.Script.comment }
  | "(*" { ignore (comment lexbuf); comment lexbuf }
  | "\"" { string_in_comment lexbuf }
  | _    { comment lexbuf }
  | eof  { raise End_of_file }

and string_in_comment = parse
  | "\"\"" { string_in_comment lexbuf }
  | "\"" { comment lexbuf }
  | _ { string_in_comment lexbuf }
  | eof  { raise End_of_file }

{
  open Ideutils

  let highlighting = ref false

  let highlight_slice (input_buffer:GText.buffer) (start:GText.iter) stop =
    starting := true; (* approximation: assume the beginning of a sentence *)
    if !highlighting then prerr_endline "Rejected highlight"
    else begin
      highlighting := true;
      prerr_endline "Highlighting slice now";
      input_buffer#remove_tag ~start ~stop Tags.Script.error;
      input_buffer#remove_tag ~start ~stop Tags.Script.kwd;
      input_buffer#remove_tag ~start ~stop Tags.Script.decl;
      input_buffer#remove_tag ~start ~stop Tags.Script.comment;

      (try begin
	let offset = start#offset in
	let s = start#get_slice ~stop in
	let convert_pos = byte_offset_to_char_offset s in
	let lb = Lexing.from_string s in
	try
	  while true do
	    let b,e,o =
	      if !starting then next_starting_order lb
	      else next_interior_order lb in

	    let b,e = convert_pos b,convert_pos e in
	    let start = input_buffer#get_iter_at_char (offset + b) in
	    let stop = input_buffer#get_iter_at_char (offset + e) in
	    input_buffer#apply_tag ~start ~stop o
	  done
	with End_of_file -> ()
      end
      with _ -> ());
      highlighting := false
    end

  let highlight_current_line input_buffer =
    try
      let i = get_insert input_buffer in
      highlight_slice input_buffer (i#set_line_offset 0) i
    with _ -> ()

  let highlight_around_current_line input_buffer =
    try
      let i = get_insert input_buffer in
      highlight_slice input_buffer
	(i#backward_lines 10)
	(ignore (i#nocopy#forward_lines 10);i)

    with _ -> ()

  let highlight_all input_buffer =
  try
    highlight_slice input_buffer input_buffer#start_iter input_buffer#end_iter
  with _ -> ()

}
