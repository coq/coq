
(* $Id$ *)

open Names
open Univ
open Generic
open Term

let lexer = {
  Token.func = Lexer.func;
  Token.using = (fun _ -> ());
  Token.removing = (fun _ -> ());
  Token.tparse = Lexer.tparse;
  Token.text = Lexer.token_text }
  
type command =
  | Definition of identifier * constr option * constr
  | Parameter of identifier * constr
  | Variable of identifier * constr
  | Inductive of 
      (identifier * constr) list *
      (identifier * constr * (identifier * constr) list) list
  | Check of constr

let gram = Grammar.create lexer

let term = Grammar.Entry.create gram "term"
let command = Grammar.Entry.create gram "command"

let new_univ =
  let uc = ref 0 in
  let univ = id_of_string "univ" in
  fun () -> incr uc; { u_sp = make_path [] univ CCI; u_num = !uc }

let path_of_string s = make_path [] (id_of_string s) CCI

EXTEND
  term: [ 
    [ id = IDENT -> 
	VAR (id_of_string id) 
    | "Set" ->
	DOP0 (Sort (Prop Pos))
    | "Prop" ->
	DOP0 (Sort (Prop Null))
    | "Type" ->
	DOP0 (Sort (Type (new_univ())))
    | IDENT "Const"; id = IDENT ->
	DOPN (Const (path_of_string id), [||])
    | IDENT "Ind"; id = IDENT; n = INT ->
	let n = int_of_string n in
	DOPN (MutInd (path_of_string id, n), [||])
    | IDENT "Construct"; id = IDENT; n = INT; i = INT ->
	let n = int_of_string n and i = int_of_string i in
	DOPN (MutConstruct ((path_of_string id, n), i), [||])
    | "["; id = IDENT; ":"; t = term; "]"; c = term ->
	DOP2 (Lambda, t, DLAM (Name (id_of_string id), c))
    | "("; id = IDENT; ":"; t = term; ")"; c = term ->
	DOP2 (Prod, t, DLAM (Name (id_of_string id), c))
  ] ];
  command: [ 
    [ "Definition"; id = IDENT; ":="; c = term; "." ->
	Definition (id_of_string id, None, c)
    | "Definition"; id = IDENT; ":"; t = term; ":="; c = term; "." ->
	Definition (id_of_string id, Some t, c)
    | "Parameter"; id = IDENT; ":"; t = term; "." ->
	Parameter (id_of_string id, t)
    | "Variable"; id = IDENT; ":"; t = term; "." ->
	Variable (id_of_string id, t)
    | IDENT "Check"; c = term; "." ->
	Check c
    | EOI -> raise End_of_file
  ] ];
END

