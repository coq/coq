(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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

  let tag_of_ident =
    let one_word_commands =
      [ "Add" ; "Check"; "Eval"; "Extraction" ;
	"Load" ; "Undo"; "Goal";
	"Proof" ; "Print";"Save" ;
	"End" ; "Section"; "Chapter"; "Transparent"; "Opaque"; "Comments" ]
    in
    let one_word_declarations =
      [ (* Definitions *)
	"Definition" ; "Let" ; "Example" ; "SubClass" ;
        "Fixpoint" ; "CoFixpoint" ; "Scheme" ; "Function" ;
        (* Assumptions *)
	"Hypothesis" ; "Variable" ; "Axiom" ; "Parameter" ; "Conjecture" ;
	"Hypotheses" ; "Variables" ; "Axioms" ; "Parameters";
        (* Inductive *)
        "Inductive" ; "CoInductive" ; "Record" ; "Structure" ;
        (* Other *)
	"Ltac" ; "Typeclasses"; "Instance"; "Include"; "Context"; "Class" ]
    in
    let proof_declarations =
      [ "Theorem" ; "Lemma" ; " Fact" ; "Remark" ; "Corollary" ;
        "Proposition" ; "Property" ]
    in
    let proof_ends =
      [ "Qed" ; "Defined" ; "Admitted"; "Abort" ]
    in
    let constr_keywords =
      [ "forall"; "fun"; "match"; "fix"; "cofix"; "with"; "for";
	"end"; "as"; "let"; "in"; "if"; "then"; "else"; "return";
	"Prop"; "Set"; "Type" ]
    in
    let h = Hashtbl.create 97 in (* for vernac *)
    let h' = Hashtbl.create 97 in (* for constr *)
    List.iter (fun s -> Hashtbl.add h s Keyword) one_word_commands;
    List.iter (fun s -> Hashtbl.add h s Declaration) one_word_declarations;
    List.iter (fun s -> Hashtbl.add h s ProofDeclaration) proof_declarations;
    List.iter (fun s -> Hashtbl.add h s Qed) proof_ends;
    List.iter (fun s -> Hashtbl.add h' s Keyword) constr_keywords;
    (fun initial id -> Hashtbl.find (if initial then h else h') id)

  exception Unterminated

  let here f lexbuf = f (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf)

}

let space =
  [' ' '\n' '\r' '\t' '\012'] (* '\012' is form-feed *)

let firstchar =
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let identchar =
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let ident = firstchar identchar*

let undotted_sep = [ '{' '}' ]

let dot_sep = '.' (space | eof)

let multiword_declaration =
  "Module" (space+ "Type")?
| "Program" space+ ident
| "Existing" space+ "Instance" "s"?
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
  | "*)" { (true, Lexing.lexeme_start lexbuf + 2) }
  | eof { (false, Lexing.lexeme_end lexbuf) }
  | _ { comment lexbuf }

and sentence initial stamp = parse
  | "(*" {
      let comm_start = Lexing.lexeme_start lexbuf in
      let trully_terminated,comm_end = comment lexbuf in
      stamp comm_start comm_end Comment;
      if not trully_terminated then raise Unterminated;
      (* A comment alone is a sentence.
	 A comment in a sentence doesn't terminate the sentence.
         Note: comm_end is the first position _after_ the comment,
	 as required when tagging a zone, hence the -1 to locate the
	 ")" terminating the comment.
      *)
      if initial then comm_end - 1 else sentence false stamp lexbuf
    }
  | "\"" {
      let str_start = Lexing.lexeme_start lexbuf in
      let str_end = coq_string lexbuf in
      stamp str_start str_end String;
      sentence false stamp lexbuf
    }
  | multiword_declaration {
      if initial then here stamp lexbuf Declaration;
      sentence false stamp lexbuf
    }
  | multiword_command {
      if initial then here stamp lexbuf Keyword;
      sentence false stamp lexbuf
    }
  | ident as id {
      (try here stamp lexbuf (tag_of_ident initial id) with Not_found -> ());
      sentence false stamp lexbuf }
  | ".." {
      (* We must have a particular rule for parsing "..", where no dot
	 is a terminator, even if we have a blank afterwards
	 (cf. for instance the syntax for recursive notation).
	 This rule and the following one also allow to treat the "..."
	 special case, where the third dot is a terminator. *)
      sentence false stamp lexbuf
    }
  | dot_sep { Lexing.lexeme_start lexbuf } (* The usual "." terminator *)
  | undotted_sep {
      (* Separators like { or } are only active at the start of a sentence *)
      if initial then Lexing.lexeme_start lexbuf
      else sentence false stamp lexbuf
    }
  | space+ {
       (* Parsing spaces is the only situation preserving initiality *)
       sentence initial stamp lexbuf
    }
  | _ {
      (* Any other characters (for instance bullets "-" "*" "+") *)
      sentence false stamp lexbuf
    }
  | eof { raise Unterminated }

{

  (** Parse a sentence in string [slice], tagging relevant parts with
      function [stamp], and returning the position of the first
      sentence delimitor (either "." or "{" or "}" or the end of a comment).
      It will raise [Unterminated] when no end of sentence is found.
  *)

  let delimit_sentence stamp slice =
    sentence true stamp (Lexing.from_string slice)

}
