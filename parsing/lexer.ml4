(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Token

(* Dictionaries: trees annotated with string options, each node being a map
   from chars to dictionaries (the subtrees). A trie, in other words. *)

module CharMap = Map.Make (struct type t = char let compare = compare end)

type ttree = { 
  node : string option;
  branch : ttree CharMap.t }

let empty_ttree = { node = None; branch = CharMap.empty }

let ttree_add ttree str =
  let rec insert tt i =
    if i == String.length str then 
      {node = Some str; branch = tt.branch}
    else
      let c = str.[i] in
      let br =
        match try Some (CharMap.find c tt.branch) with Not_found -> None with
          | Some tt' ->
              CharMap.add c (insert tt' (i + 1)) (CharMap.remove c tt.branch)
          | None ->
              let tt' = {node = None; branch = CharMap.empty} in
              CharMap.add c (insert tt' (i + 1)) tt.branch
      in
      { node = tt.node; branch = br }
  in 
  insert ttree 0

(* Search a string in a dictionary: raises [Not_found]
   if the word is not present. *)

let ttree_find ttree str =
  let rec proc_rec tt i =
    if i == String.length str then
      match tt.node with
	| Some s -> s
	| None -> raise Not_found
    else 
      proc_rec (CharMap.find str.[i] tt.branch) (i+1)
  in 
  proc_rec ttree 0

(* Lexer conventions on tokens *)

type error =
  | Illegal_character
  | Unterminated_comment
  | Unterminated_string
  | Undefined_token
  | Bad_token of string

exception Error of error

let bad_token str = raise (Error (Bad_token str))

let check_special_token str =
  let rec loop = parser
    | [< ' (' ' | '\n' | '\r' | '\t') >] -> bad_token str
    | [< _ = Stream.empty >] -> ()
    | [< '_ ; s >] -> loop s
  in
  loop (Stream.of_string str)

let check_ident str =
  let rec loop = parser
    | [< ''$' | 'a'..'z' | 'A'..'Z' | '\192'..'\214' | '\216'..'\246'
              | '\248'..'\255' | '0'..'9' | ''' | '_'; s >] -> loop s
    | [< _ = Stream.empty >] -> ()
    | [< >] -> bad_token str
  in
  loop (Stream.of_string str)

(* Special token dictionary *)
let token_tree = ref empty_ttree

let add_special_token str =
  check_special_token str;
  token_tree := ttree_add !token_tree str

(* Keyword identifier dictionary *)
let keywords = ref empty_ttree

let find_keyword s = ttree_find !keywords s

let add_keyword str =
  check_ident str;
  keywords := ttree_add !keywords str

let is_keyword s = 
  try let _ = ttree_find !keywords s in true with Not_found -> false


(* Adding a new token (keyword or special token). *)
let add_token (con, str) = match con with
  | "" ->
      let normal_token =
        if String.length str > 0 then
          match str.[0] with
	    | ' ' | '\n' | '\r' | '\t' | '0'..'9' | '"' -> bad_token str
            | '_' | '$' | 'a'..'z' | 'A'..'Z' -> true
            | _ -> false
        else 
	  true
      in
      if normal_token then add_keyword str else add_special_token str
  | "METAIDENT" | "IDENT" | "FIELD" | "INT" | "STRING" | "EOI"
      -> ()
  | _ ->
      raise (Token.Error ("\
the constructor \"" ^ con ^ "\" is not recognized by Lexer"))


(* Freeze and unfreeze the state of the lexer *)
type frozen_t = ttree * ttree

let freeze () = (!keywords, !token_tree)

let unfreeze (kw,tt) =
  keywords := kw;
  token_tree := tt

let init () =
  unfreeze (empty_ttree, empty_ttree);
  List.iter add_keyword
    [ "Grammar"; "Syntax"; "Quit"; "Load"; "Compile";
      "of"; "with"; "end"; "as"; "in"; "using";
      "Cases"; "Fixpoint"; "CoFixpoint";
      "Definition"; "Inductive"; "CoInductive"; 
      "Theorem"; "Variable"; "Axiom"; "Parameter"; "Hypothesis";
      "Orelse"; "Proof"; "Qed";
      "Prop"; "Set"; "Type"; "And"
    ]; (* "let" is not a keyword because #Core#let.cci would not parse *)
  List.iter add_special_token 
    [ ":"; "("; ")"; "["; "]"; "{"; "}"; "_"; ";"; "`"; "``"; 
      "()"; "->"; "\\/"; "/\\"; "|-"; ":="; "<->"; "!"; "$"; "%"; "&";
      "*"; "+"; ","; "@"; "^"; "#"; "\\"; "/"; "-"; "<"; ">"; 
      "|"; "?"; "="; "~"; "'"; "<<"; ">>"; "<>"; "::";
      "<:"; ":<"; "=>"; ">->" ]

let _ = init()

(* Errors occuring while lexing (explained as "Lexer error: ...") *)
let err loc str = Stdpp.raise_with_loc loc (Error str)

(* The string buffering machinery *)

let buff = ref (String.create 80)

let store len x =
  if len >= String.length !buff then
    buff := !buff ^ String.create (String.length !buff);
  !buff.[len] <- x;
  succ len

let mstore len s =
  let rec add_rec len i =
    if i == String.length s then len else add_rec (store len s.[i]) (succ i)
  in
  add_rec len 0

let get_buff len = String.sub !buff 0 len


(* The classical lexer: idents, numbers, quoted strings, comments *)

let rec ident len = parser
  | [< ' ('a'..'z' | 'A'..'Z' | '\192'..'\214' | '\216'..'\246' 
         |'\248'..'\255' | '0'..'9' | ''' | '_' | '@' as c); s >] ->
      ident (store len c) s
  | [< >] -> len

let rec number len = parser
  | [< ' ('0'..'9' as c); s >] -> number (store len c) s
  | [< >] -> len

let escape len c = store len c

let rec string bp len = parser
  | [< ''"' >] -> len
(* Uncomment to allow '"' in strings
  | [< ''\\'; c = (parser [< ' ('"' | '\\' as c) >] -> c | [< >] -> '\\'); s >]
     -> string bp (escape len c) s
*)
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_string
  | [< 'c; s >] -> string bp (store len c) s 

let rec comment bp = parser
  | [< ''(';
       _ = (parser
              | [< ''*'; _ = comment bp >] -> ()
              | [< >] -> ()); 
       s >] -> comment bp s
  | [< ''*';
       _ = parser
         | [< '')' >] -> ()
         | [< s >] -> comment bp s >] -> ()
  | [< ''"'; _ = (parser bp [< _ = string bp 0 >] -> ()); s >] ->
      comment bp s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_comment
  | [< '_; s >] -> comment bp s 

(* Parse a special token, using the [token_tree] *)

let process_chars bp c cs =
  let rec proc_rec tt =
    match
      match Stream.peek cs with
	| Some c -> 
	    (try Some (CharMap.find c tt.branch) with Not_found -> None)
	| None -> None
    with
      | Some tt' -> Stream.junk cs; proc_rec tt'
      | None -> tt.node
  in
  let t =
    try proc_rec (CharMap.find c !token_tree.branch) 
    with Not_found -> !token_tree.node
  in
  let ep = Stream.count cs in
  match t with
    | Some t -> (("", t), (bp, ep))
    | None -> err (bp, ep) Undefined_token

(* Parse a token in a char stream *)

let rec next_token = parser bp
  | [< '' ' | '\n' | '\r'| '\t'; s >] -> next_token s
  | [< ''$'; len = ident (store 0 '$') >] ep -> 
      (("METAIDENT", get_buff len), (bp,ep))
  | [< ''.'; t = parser
	 | [< ' ('_' | 'a'..'z' | 'A'..'Z' | '\192'..'\214' 
		| '\216'..'\246' | '\248'..'\255' as c);
	      len = ident (store 0 c) >] -> ("FIELD", get_buff len)
	 | [< >] -> ("", ".") >] ep -> (t, (bp,ep))
  | [< ' ('_' | 'a'..'z' | 'A'..'Z' | '\192'..'\214' 
         | '\216'..'\246' | '\248'..'\255' as c);
       len = ident (store 0 c) >] ep ->
      let id = get_buff len in
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
  | [< ' ('0'..'9' as c); len = number (store 0 c) >] ep ->
      (("INT", get_buff len), (bp, ep))
  | [< ''"'; len = string bp 0 >] ep ->
      (("STRING", get_buff len), (bp, ep))
  | [< ' ('(' as c);
       t = parser
         | [< ''*'; _ = comment bp; s >] -> next_token s
         | [< t = process_chars bp c >] -> t >] -> t
  | [< 'c; t = process_chars bp c >] -> t
  | [< _ = Stream.empty >] -> (("EOI", ""), (bp, bp + 1))

(* Location table system for creating tables associating a token count
   to its location in a char stream (the source) *)

let locerr () = invalid_arg "Lexer: location function"

let loct_create () = ref (Array.create 1024 None)

let loct_func loct i =
  match
    if i < 0 || i >= Array.length !loct then None
    else Array.unsafe_get !loct i
  with
    | Some loc -> loc
    | _ -> locerr ()

let loct_add loct i loc =
  if i >= Array.length !loct then begin
    let new_tmax = Array.length !loct * 2 in
    let new_loct = Array.create new_tmax None in
    Array.blit !loct 0 new_loct 0 (Array.length !loct);
    loct := new_loct
  end;
  !loct.(i) <- Some loc

let func cs =
  let loct = loct_create () in
  let ts =
    Stream.from
      (fun i ->
         let (tok, loc) = next_token cs in
	 loct_add loct i loc; Some tok)
  in
  (ts, loct_func loct)

(* Names of tokens, for this lexer, used in Grammar error messages *)

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
  (*i was
  if p_prm = "" then
    (parser [< '(con, prm) when con = p_con >] -> prm)
  else
    (parser [< '(con, prm) when con = p_con && prm = p_prm >] -> prm)
  i*)
