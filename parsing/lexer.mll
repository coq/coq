
(* $Id$ *)

{
open Util

type error =
  | Illegal_character
  | Unterminated_comment
  | Unterminated_string

exception Error of error

(* token trees *)

module Charmap = Map.Make (struct type t = char let compare = compare end)

type ttree = { node : string option; branch : ttree Charmap.t }

let ttree_empty = { node = None; branch = Charmap.empty }

let ttree_add ttree str =
  let n = String.length str in
  let rec insert tt i =
    if i == n then 
      { node = Some str; branch = tt.branch }
    else
      let c = str.[i] in
      let br =
        match 
	  try Some (Charmap.find c tt.branch) with Not_found -> None
        with
          | Some tt' ->
              Charmap.add c (insert tt' (i + 1)) (Charmap.remove c tt.branch)
          | None ->
              let tt' = { node = None; branch = Charmap.empty } in
              Charmap.add c (insert tt' (i + 1)) tt.branch
      in
      { node = tt.node; branch = br }
  in 
  insert ttree 0

let ttree_find ttree str =
  let n = String.length str in
  let rec proc_rec tt i =
    if i == n then
      match tt.node with
	| Some s -> s
      	| None -> raise Not_found
    else 
      proc_rec (Charmap.find str.[i] tt.branch) (i+1)
  in 
  proc_rec ttree 0

let kw_table = ref ttree_empty

let init () =
  kw_table := ttree_empty;
  List.iter 
    (fun kw -> kw_table := ttree_add !kw_table kw)
    [ "Grammar"; "Syntax"; "Quit"; "Load"; "Compile";
      "of"; "with"; "end"; "as"; "in"; "using";
      "Cases"; "Fixpoint"; "CoFixpoint";
      "Definition"; "Inductive"; "CoInductive"; 
      "Theorem"; "Variable"; "Axiom"; "Parameter"; "Hypothesis";
      "Orelse"; "Proof"; "Qed";
      "Prop"; "Set"; "Type" ]  

let _ = init ()

let add_keyword s = kw_table := ttree_add !kw_table s

let is_keyword s = 
  try let _ = ttree_find !kw_table s in true with Not_found -> false

type frozen_t = ttree

let freeze () = !kw_table

let unfreeze ft = kw_table := ft

let char_for_backslash =
  match Sys.os_type with
  | "Unix" | "Win32" ->
      begin function
      | 'n' -> '\010'
      | 'r' -> '\013'
      | 'b' -> '\008'
      | 't' -> '\009'
      | c   -> c
      end
  | "MacOS" ->
      begin function
      | 'n' -> '\013'
      | 'r' -> '\010'
      | 'b' -> '\008'
      | 't' -> '\009'
      | c   -> c
      end
  | x -> error "Lexer: unknown system type"

let char_for_decimal_code lexbuf i =
  let c = 100 * (Char.code(Lexing.lexeme_char lexbuf i) - 48) +
           10 * (Char.code(Lexing.lexeme_char lexbuf (i+1)) - 48) +
                (Char.code(Lexing.lexeme_char lexbuf (i+2)) - 48) in  
  Char.chr(c land 0xFF)

let string_buffer = Buffer.create 80
let string_start_pos = ref 0
			 
let comment_depth = ref 0
let comment_start_pos = ref 0

}

let blank = [' ' '\010' '\013' '\009' '\012']
let firstchar = 
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let identchar = 
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' 
   '\'' '0'-'9']
let symbolchar = ['!' '$' '%' '&' '*' '+' ',' '@' '^' '~' '#']
let extrachar = symbolchar | ['\\' '/' '-' '<' '>' '|' ':' '?' '=']
let decimal_literal = ['0'-'9']+
let hex_literal = '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
let oct_literal = '0' ['o' 'O'] ['0'-'7']+
let bin_literal = '0' ['b' 'B'] ['0'-'1']+

rule token = parse
  | blank+ 
      { token lexbuf }
  | firstchar identchar* 
      { let s = Lexing.lexeme lexbuf in
	if is_keyword s then ("",s) else ("IDENT",s) }
  | decimal_literal | hex_literal | oct_literal | bin_literal
      { ("INT", Lexing.lexeme lexbuf) }
  | "(" | ")" | "[" | "]" | "{" | "}" | "." | "_" | ";"| "`" | "()" | "'("
  | "->" | "\\/" | "/\\" | "|-" | ":=" | "<->" | extrachar
      { ("", Lexing.lexeme lexbuf) }
  | ('\\' (symbolchar | '\\' | '-' | '>' | '|' | ':' | '?' | '=' | '<')+ |
     '/'  (symbolchar | '/'  | '-' | '>' | '|' | ':' | '?' | '=' | '<')+ |
     '-'  (symbolchar | '\\' | '/' | '-' | '|' | ':' | '?' | '=' | '<')+ |
     '|'  (symbolchar | '\\' | '/' | '|' | '>' | ':' | '?' | '=' | '<')+ |
     '='  (symbolchar | '\\' | '/' | '|' | '-' | '>' | ':' | '=' | '<')+ |
     ':'  (symbolchar | '\\' | '/' | '|' | '-' | '>' | ':' | '=' | '<')+ |
     '<'  (symbolchar | '\\' | '/' | '|' | '>' | '?' | ':' | '=' | '<')+ |
     "<-" (symbolchar | '\\' | '/' | '|' | '-' | '?' | ':' | '=' | '<')+ |
     '>' | '?') extrachar* | "<-"
    { ("", Lexing.lexeme lexbuf) }
  | symbolchar+ extrachar*
    { ("", Lexing.lexeme lexbuf) }
  (***
  | '`' [^'`']* '`'
      { let s = Lexing.lexeme lexbuf in
	("QUOTED", String.sub s 1 (String.length s - 2)) }
  ***)
  | "\""
      { Buffer.reset string_buffer;
        let string_start = Lexing.lexeme_start lexbuf in
        string_start_pos := string_start;
        string lexbuf;
        ("STRING", Buffer.contents string_buffer) }
  | "(*"
      { comment_depth := 1;
        comment_start_pos := Lexing.lexeme_start lexbuf;
        comment lexbuf;
        token lexbuf }
  | eof 
      { ("EOI","") }
  | _ { let loc = (Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf) in
	raise (Stdpp.Exc_located (loc, Error Illegal_character)) }

and comment = parse
  | "(*"
      { comment_depth := succ !comment_depth; comment lexbuf }
  | "*)"
      { comment_depth := pred !comment_depth;
        if !comment_depth > 0 then comment lexbuf }
  | "\""
      { Buffer.reset string_buffer;
        string_start_pos := Lexing.lexeme_start lexbuf;
        string lexbuf;
        comment lexbuf }
  | "''"
      { comment lexbuf }
  | "'" [^ '\\' '\''] "'"
      { comment lexbuf }
  | "'\\" ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { comment lexbuf }
  | "'\\" ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { comment lexbuf }
  | eof
      { let loc = (!comment_start_pos, !comment_start_pos+2) in
	raise (Stdpp.Exc_located (loc, Error Unterminated_comment)) }
  | _
      { comment lexbuf }

and string = parse
  | '"'
      { () }
  | '\\' ("\010" | "\013" | "\013\010") [' ' '\009'] *
      { string lexbuf }
  | '\\' ['\\' '"' 'n' 't' 'b' 'r']
      { let c = char_for_backslash (Lexing.lexeme_char lexbuf 1) in
	Buffer.add_char string_buffer c;
        string lexbuf }
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
      { Buffer.add_char string_buffer (char_for_decimal_code lexbuf 1);
        string lexbuf }
  | eof
      { let loc = (!string_start_pos, !string_start_pos+1) in
	raise (Stdpp.Exc_located (loc, Error Unterminated_string)) }
  | _
      { Buffer.add_char string_buffer (Lexing.lexeme_char lexbuf 0);
        string lexbuf }

{

let create_loc_table () = ref (Array.create 1024 None)

let find_loc t i = 
  if i < 0 || i >= Array.length !t then invalid_arg "find_loc";
  match Array.unsafe_get !t i with 
    | None -> invalid_arg "find_loc" 
    | Some l -> l

let add_loc t i l =
  while i >= Array.length !t do
    let new_t = Array.create (2 * Array.length !t) None in
    Array.blit !t 0 new_t 0 (Array.length !t);
    t := new_t
  done;
  !t.(i) <- Some l
  
let func cs =
  let loct = create_loc_table () in
  let lexbuf = 
    Lexing.from_function 
      (fun s _ -> match cs with parser 
	 | [< 'c >] -> String.unsafe_set s 0 c; 1
	 | [< >] -> 0)
  in
  let next_token i = 
    let tok = token lexbuf in
    let loc = (Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf) in
    add_loc loct i loc; Some tok
  in
  let ts = Stream.from next_token in
  (ts, find_loc loct)

let is_ident s =
  String.length s > 0 &&
  (match s.[0] with
     | '$' | 'A'..'Z' | 'a'..'z' | '\192'..'\214' | '\216'..'\246' 
     | '\248'..'\255' -> true
     | _ -> false)

let add_token = function
  | ("",kw) -> if is_ident kw then add_keyword kw
  | _ -> ()
	 
let token_text = function
  | ("", t) -> "'" ^ t ^ "'"
  | ("IDENT", "") -> "identifier"
  | ("IDENT", t) -> "'" ^ t ^ "'"
  | ("INT", "") -> "integer"
  | ("INT", s) -> "'" ^ s ^ "'"
  | ("STRING", "") -> "string"
  | ("EOI", "") -> "end of input"
  | (con, "") -> con
  | (con, prm) -> con ^ " \"" ^ prm ^ "\""

let tparse (p_con, p_prm) =
  None
  (*i etait en ocaml 2.xx :
    if p_prm = "" then
      parser [< '(con, prm) when con = p_con >] -> prm
    else
      parser [< '(con, prm) when con = p_con && prm = p_prm >] -> prm
  i*)

}
