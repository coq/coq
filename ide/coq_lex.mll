(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

{
  open Lexing

  type token =
    | Comment
    | Keyword
    | Declaration
    | ProofDeclaration
    | Qed
    | String

  (* Without this table, the automaton would be too big and
     ocamllex would fail *)
  let is_one_word_command =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [  "Add" ; "Check"; "Eval"; "Extraction" ;
	 "Load" ; "Undo"; "Goal";
	 "Proof" ; "Print";"Save" ;
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
	[ (* Definitions *)
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

  let is_proof_declaration =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [ "Theorem" ; "Lemma" ; " Fact" ; "Remark" ; "Corollary" ;
        "Proposition" ; "Property" ];
    Hashtbl.mem h

  let is_proof_end =
    let h = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add h s ())
      [ "Qed" ; "Defined" ; "Admitted" ];
    Hashtbl.mem h

  let start = ref true
  let last_leading_blank = ref 0
}

let space =
  [' ' '\010' '\013' '\009' '\012']

let firstchar =
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let identchar =
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let ident = firstchar identchar*

let sentence_sep = '.' [ ' ' '\n' '\t' ]

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
  | "\"" { Lexing.lexeme_end lexbuf }
  | eof { Lexing.lexeme_end lexbuf }
  | _ { coq_string lexbuf }

and comment = parse
  | "(*" { ignore (comment lexbuf); comment lexbuf }
  | "\"" { ignore (coq_string lexbuf); comment lexbuf }
  | "*)" { Lexing.lexeme_end lexbuf }
  | eof { Lexing.lexeme_end lexbuf }
  | _ { comment lexbuf }

and sentence stamp = parse
  | space+ {
      if !start then last_leading_blank := Lexing.lexeme_end lexbuf;
      sentence stamp lexbuf
    }
  | "(*" {
      let comm_start = Lexing.lexeme_start lexbuf in
      let comm_end = comment lexbuf in
      if !start then last_leading_blank := comm_end;
      stamp comm_start comm_end Comment;
      sentence stamp lexbuf
    }
  | "\"" {
      let str_start = Lexing.lexeme_start lexbuf in
      let str_end = coq_string lexbuf in
      stamp str_start str_end String;
      start := false;
      sentence stamp lexbuf
    }
  | multiword_declaration {
      if !start then begin
        start := false;
        stamp (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf) Declaration
      end;
      sentence stamp lexbuf
    }
  | multiword_command {
      if !start then begin
        start := false;
        stamp (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf) Keyword
      end;
      sentence stamp lexbuf }
  | ident as id {
      if !start then begin
        start := false;
        if id <> "Time" then begin
            if is_proof_end id then
              stamp (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf) Qed
            else if is_one_word_command id then
              stamp (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf) Keyword
            else if is_one_word_declaration id then
              stamp (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf) Declaration
            else if is_proof_declaration id then
              stamp (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf) ProofDeclaration
        end
      end else begin
        if is_constr_kw id then
	  stamp (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf) Keyword
      end;
      sentence stamp lexbuf }
  | ".."
  | _    { sentence stamp lexbuf}
  | sentence_sep { }
  | eof { raise Not_found }

{
  let find_end_offset stamp slice =
    let lb = Lexing.from_string slice in
    start := true;
    last_leading_blank := 0;
    sentence stamp lb;
    !last_leading_blank,Lexing.lexeme_end lb
}
