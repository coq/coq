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

  type color = string

  type highlight_order = int * int * color

  let comment_start = ref 0

  let is_keyword =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [  "Add" ; "Check"; "Defined" ; 
	 "End" ; "Eval"; "Export" ; "Extraction" ; "Hint" ; "Hints" ;
	 "Implicits" ; "Import" ; 
	 "Infix" ; "Load" ; "Module" ;
	 "Notation"; "Proof" ; "Print"; "Qed" ;
	 "Require" ; "Reset"; "Undo"; "Save" ;
	 "Section" ; "Unset" ;
	 "Set" ; "Notation";
	 "Implicit"; "Arguments"; "Unfold"; "Resolve"
      ];
    Hashtbl.mem h

  let is_constr_kw =
    let h = Hashtbl.create 97 in
      List.iter (fun s -> Hashtbl.add h s ())
	[ "forall"; "fun"; "match"; "fix"; "cofix"; "with"; "for"; 
	  "end"; "as"; "let"; "in"; "dest"; "if"; "then"; "else"; "return";
	  "Prop"; "Set"; "Type"]; 
      Hashtbl.mem h

  let is_declaration =
    let h = Hashtbl.create 97 in
      List.iter (fun s -> Hashtbl.add h s ())
	[ "Theorem" ; "Lemma" ; "Fact" ; "Remark" ; "Corollary" ; "Proposition" ; "Property" ;
	  "Definition" ; "Let" ; "Example" ; "SubClass" ; "Inductive" ; "CoInductive" ; 
	  "Record" ; "Structure" ; "Fixpoint" ; "CoFixpoint"; 
	  "Hypothesis" ; "Variable" ; "Axiom" ; "Parameter" ; "Conjecture" ;
	  "Hypotheses" ; "Variables" ; "Axioms" ; "Parameters"
	];
      Hashtbl.mem h

}

let space = 
  [' ' '\010' '\013' '\009' '\012']
let firstchar = 
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let identchar = 
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let ident = firstchar identchar*

let thm_token = "Theorem" | "Lemma" | "Fact" | "Remark" | "Corollary" | "Proposition" | "Property"

let def_token = "Definition" | "Let" | "Example" | "SubClass"

let assumption = "Hypothesis" | "Variable" | "Axiom" | "Parameter" | "Conjecture" |
  "Hypotheses" | "Variables" | "Axioms" | "Parameters"

let declaration = 
  "Theorem" | "Lemma" | "Fact" | "Remark" | "Corollary" | "Proposition" | "Property" |
  "Definition" | "Let" | "Example" | "SubClass" |
  "Inductive" | "CoInductive" | 
  "Record" | "Structure" |
  "Fixpoint" | "CoFixpoint"
       

rule next_order = parse
  | "(*" 
      { comment_start := lexeme_start lexbuf; comment lexbuf }
  | "Module Type"
      { lexeme_start lexbuf, lexeme_end lexbuf, "kwd" }
  | "Program" space+ ident { lexeme_start lexbuf, lexeme_end lexbuf, "decl" }
  | ident as id 
      { if is_keyword id then 
	    lexeme_start lexbuf, lexeme_end lexbuf, "kwd" 
	else 
	    begin
	      if is_constr_kw id then
		lexeme_start lexbuf, lexeme_end lexbuf, "kwd"
	      else
		begin
		  if is_declaration id then
		    lexeme_start lexbuf, lexeme_end lexbuf, "decl"
		  else
		    next_order lexbuf 
		end
	    end
      }
  | _    { next_order lexbuf}
  | eof  { raise End_of_file }

and comment = parse
  | "*)" { !comment_start,lexeme_end lexbuf,"comment" }
  | "(*" { ignore (comment lexbuf); comment lexbuf }
  | _    { comment lexbuf }
  | eof  { raise End_of_file }

{
  open Ideutils

  let highlighting = ref false

  let highlight_slice (input_buffer:GText.buffer) (start:GText.iter) stop = 
    if !highlighting then prerr_endline "Rejected highlight" 
    else begin
      highlighting := true;
      prerr_endline "Highlighting slice now";
      input_buffer#remove_tag_by_name ~start ~stop "error";
      input_buffer#remove_tag_by_name ~start ~stop "kwd";
      input_buffer#remove_tag_by_name ~start ~stop "decl";
      input_buffer#remove_tag_by_name ~start ~stop "comment";

      (try begin
	let offset = start#offset in
	let s = start#get_slice ~stop in
	let convert_pos = byte_offset_to_char_offset s in
	let lb = Lexing.from_string s in
	try 
	  while true do
	    let b,e,o=next_order lb in
	    let b,e = convert_pos b,convert_pos e in
	    let start = input_buffer#get_iter_at_char (offset + b) in
	    let stop = input_buffer#get_iter_at_char (offset + e) in
	    input_buffer#apply_tag_by_name ~start ~stop o 
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
