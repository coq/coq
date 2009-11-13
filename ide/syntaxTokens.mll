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

  type markup =
    | Keyword of (int*int)
    | Declaration of (int*int)

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
	  "end"; "as"; "let"; "in"; "if"; "then"; "else"; "return";
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
| "Extraction" space+ (("Language" space+ ("Ocaml"|"Haskell"|"Scheme"|"Toplevel"))|
    ("Library"|"Inline"|"NoInline"|"Blacklist"))
| "Recursive" space+ "Extraction" (space+ "Library")?
| ("Print"|"Reset") space+ "Extraction" space+ ("Inline"|"Blacklist")
| "Extract" space+ (("Inlined" space+) "Constant"| "Inductive")

(* At least still missing: "Inline" + decl, variants of "Identity
  Coercion", variants of Print, Add, ... *)

rule coq_string = parse
  | "\"\"" { coq_string lexbuf }
  | "\"" { }
  | _ { coq_string lexbuf }
  | eof { }

and comment = parse
  | "(*" { comment lexbuf; comment lexbuf }
  | "*)" { }
  | "\"" { coq_string lexbuf; comment lexbuf }
  | _ { comment lexbuf }
  | eof { }

and sentence tag_cb = parse
  | "(*" { comment lexbuf; sentence tag_cb lexbuf }
  | "\"" { coq_string lexbuf; start := false; sentence tag_cb lexbuf }
  | space+ { sentence tag_cb lexbuf }
  | multiword_declaration {
      if !start then begin
        start := false;
        tag_cb Declaration (lexeme_start lexbuf) (lexeme_end lexbuf)
      end;
      inside_sentence lexbuf }
  | multiword_command {
      if !start then begin
        start := false;
        tag_cb Keyword (lexeme_start lexbuf) (lexeme_end lexbuf)
      end;
      sentence tag_cb lexbuf }
  | ident as id {
      if !start then begin
        start := false;
        if id <> "Time" then begin
            if is_one_word_command id then
              tag_cb Keyword (lexeme_start lexbuf) (lexeme_end lexbuf)
            else if is_one_word_declaration id then
              tag_cb Declaration (lexeme_start lexbuf) (lexeme_end lexbuf)
        end
      end else begin
        if is_constr_kw id then
	  tag_cb Keyword (lexeme_start lexbuf) (lexeme_end lexbuf);
      end;
      sentence tag_cb lexbuf }
  | _    { sentence tag_cb lexbuf}
  | eof { }

{
  let parse tag_cb slice =
    let lb = from_string slice in
    start := true;
    sentence tag_cb lb
}
