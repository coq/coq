(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
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
    | [< ' ('$' | 'a'..'z' | 'A'..'Z' | '0'..'9' | ''' | '_'); s >] -> loop s
    (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
    | [< ' ('\206' | '\207'); ' ('\128'..'\191'); s >] -> loop s
    (* iso 8859-1 accentuated letters *)
    | [< ' ('\192'..'\214' | '\216'..'\246' | '\248'..'\255'); s >] -> loop s
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

let is_normal_token str =
  if String.length str > 0 then
    match str.[0] with
      | ' ' | '\n' | '\r' | '\t' | '0'..'9' | '"' -> bad_token str
      | '_' | '$' | 'a'..'z' | 'A'..'Z' -> true
	  (* utf-8 symbols of the form "E2 xx xx" [E2=226] *)
      | '\226' when String.length str > 2 ->
	  (match str.[1], str.[2] with
	    | ('\132', '\128'..'\191') | ('\133', '\128'..'\143') ->
		(* utf8 letter-like unicode 2100-214F *) true
	    | (('\136'..'\143' | '\152'..'\155'),_) ->
		(* utf8 mathematical operators unicode 2200-22FF *)
		(* utf8 miscellaneous technical unicode 2300-23FF *)
		(* utf8 miscellaneous symbols unicode 2600-26FF *)
		false
	    | _ ->
		(* default to iso 8859-1 "â" *)
		true)
	  (* iso 8859-1 accentuated letters *)
      | '\192'..'\214' | '\216'..'\246' | '\248'..'\255' -> true
      | _ -> false
  else 
    bad_token str

(* Adding a new token (keyword or special token). *)
let add_token (con, str) = match con with
  | "" ->
      if is_normal_token str then add_keyword str else add_special_token str
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
  | [< ' ('a'..'z' | 'A'..'Z' | '0'..'9' | ''' | '_' | '@' as c); s >] ->
      ident (store len c) s
  (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
  | [< ' ('\206' | '\207' as c1); ' ('\128'..'\191' as c2) ; s >] ->
      ident (store (store len c1) c2) s
  (* iso 8859-1 accentuated letters *)
  | [< ' ('\192'..'\214' | '\216'..'\246' | '\248'..'\255' as c); s >] -> 
      ident (store len c) s
  | [< >] -> len

let rec number len = parser
  | [< ' ('0'..'9' as c); s >] -> number (store len c) s
  | [< >] -> len

let escape len c = store len c

let rec string bp len = parser
  | [< ''"' >] -> len
  | [< ''\\'; c = (parser [< ' ('"' | '\\' as c) >] -> c | [< >] -> '\\'); s >]
     -> string bp (escape len c) s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_string
  | [< 'c; s >] -> string bp (store len c) s 

let comments = ref None

type commentar =
  | InVernac
  | InVernacEsc of string
  | BeVernac of string
  | InComment of string

let current = ref (BeVernac "")

let add_comment () = let reinit () = match ! current with
  | InVernac -> ()
  | InVernacEsc s -> current := InVernacEsc ""
  | BeVernac s -> current := BeVernac ""
  | InComment s -> current := InComment "" in
match (!comments,!current) with
  | None , InVernac -> ()
  | None , BeVernac s | None , InComment s | None , InVernacEsc s -> reinit (); comments := Some [str s]
  | Some _ , InVernac -> ()
  | Some l , BeVernac s | Some l , InComment s | Some l , InVernacEsc s -> reinit (); comments := Some (str s::l)

let add_comment_pp s = match !comments with
  | None -> comments := Some [s]
  | Some l -> comments := Some (s::l) 

let add_string s = match !current with
  | InVernac -> ()
  | InVernacEsc t -> current := InVernacEsc (t^s)
  | BeVernac t -> current := BeVernac (t^s)
  | InComment t -> current := InComment (t^s)
	
let rec comment bp = parser
  | [< ''(';
       _ = (parser
              | [< ''*'; s >] -> add_string "(*"; comment bp s
              | [< >] -> add_string "(" ); 
       s >] -> comment bp s
  | [< ''*';
       _ = parser
         | [< '')' >] -> add_string "*)"; add_comment ()
         | [< s >] -> add_string "*"; comment bp s >] -> ()
  | [< ''"'; _ = (parser bp [< _ = string bp 0 >] -> ()); s >] ->
      comment bp s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_comment
  | [< '_ as z; s >] -> 
	(match z with
	| '\n' | '\t' -> add_comment (); add_comment_pp (fnl ())
	| _ -> add_string (String.make 1 z)); comment bp s 

(* Parse a special token, using the [token_tree] *)

let progress_special c = function
  | None -> None
  | Some tt -> try Some (CharMap.find c tt.branch) with Not_found -> None

let rec special tt cs = match tt with
  | None -> None
  | Some tt ->
      match
	match Stream.peek cs with
	  | Some c -> 
	      (try Some (CharMap.find c tt.branch) with Not_found -> None)
	  | None -> None
      with
	| Some _ as tt' -> Stream.junk cs; special tt' cs
	| None -> tt.node

let process_chars bp c cs =
  let t =
    try special (Some (CharMap.find c !token_tree.branch)) cs
    with Not_found -> !token_tree.node
  in
  let ep = Stream.count cs in
  match t with
    | Some t -> (("", t), (bp, ep))
    | None -> err (bp, ep) Undefined_token

type token_226_tail =
  | TokSymbol of string option
  | TokIdent of string

let parse_226_tail tk = parser
  | [< ''\132' as c2; ' ('\128'..'\191' as c3);
      (* utf8 letter-like unicode 2100-214F *)
      len = ident (store (store (store 0 '\226') c2) c3) >] ->
      TokIdent (get_buff len) 
  | [< ''\133' as c2; ' ('\128'..'\143' as c3);
      (* utf8 letter-like unicode 2100-214F *)
      len = ident (store (store (store 0 '\226') c2) c3) >] ->
      TokIdent (get_buff len) 
  | [< ' ('\136'..'\143' | '\152'..'\155' as c2); 'c3;
      (* utf8 mathematical operators unicode 2200-22FF *)
      (* utf8 miscellaneous technical unicode 2300-23FF *)
      (* utf8 miscellaneous symbols unicode 2600-26FF *)
      t = special (progress_special c3 (progress_special c2 
	(progress_special '\226' tk))) >] ->
      TokSymbol t
  | [< len = ident (store 0 '\226') >] ->
      TokIdent (get_buff len)

(* Parse a token in a char stream *)

let rec next_token = parser bp
  | [< ''\n'; s >] -> (match !current with
	| BeVernac s -> current := InComment s
	| InComment _ -> add_comment_pp (fnl ())
	| _ -> ()); next_token s
  | [< '' ' | '\t'; s >] -> (match !current with
	| BeVernac _ |  InComment _ -> add_comment_pp (spc ())
	| _ -> ()); next_token s
  | [< ''\r'; s >] -> next_token s
  | [< ''$'; len = ident (store 0 '$') >] ep -> 
      (("METAIDENT", get_buff len), (bp,ep))
  | [< ''.' as c; t = parser
	 | [< ' ('_' | 'a'..'z' | 'A'..'Z' as c); len = ident (store 0 c) >] ->
	     ("FIELD", get_buff len)
	 (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
	 | [< ' ('\206' | '\207' as c1); ' ('\128'..'\191' as c2); 
	   len = ident (store (store 0 c1) c2) >] ->
	     ("FIELD", get_buff len)
         (* utf-8 mathematical symbols have format E2 xx xx [E2=226] *)
	 | [< ''\226' as c1; t = parse_226_tail 
	     (progress_special '.' (Some !token_tree)) >] ep ->
	     (match t with
	       | TokSymbol (Some t) -> ("", t)
	       | TokSymbol None -> err (bp, ep) Undefined_token
	       | TokIdent t -> ("FIELD", t))
	 (* iso 8859-1 accentuated letters *)
	 | [< ' ('\192'..'\214' | '\216'..'\246' | '\248'..'\255' as c);
	   len = ident (store 0 c) >] ->
	     ("FIELD", get_buff len)
(*
	 | [< >] -> ("", ".") >] ep -> (t, (bp,ep))
*)
	 | [< (t,_) = process_chars bp c >] -> t >] ep ->
      current:=BeVernac ""; (t, (bp,ep))
  | [< ' ('_' | 'a'..'z' | 'A'..'Z' as c); len = ident (store 0 c) >] ep ->
      let id = get_buff len in current:=InVernac; 
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
  (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
  | [< ' ('\206' | '\207' as c1); ' ('\128'..'\191' as c2); 
	   len = ident (store (store 0 c1) c2) >] ep ->
      let id = get_buff len in current:=InVernac; 
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
  (* utf-8 mathematical symbols have format E2 xx xx [E2=226] *)
  | [< ''\226' as c1; t = parse_226_tail (Some !token_tree) >] ep ->
      (match t with
	| TokSymbol (Some t) -> ("", t), (bp, ep)
	| TokSymbol None -> err (bp, ep) Undefined_token
	| TokIdent id ->
	    current:=InVernac; 
	    (try ("", find_keyword id) with Not_found -> ("IDENT", id)),
	    (bp, ep))
  (* iso 8859-1 accentuated letters *)
  | [< ' ('\192'..'\214' | '\216'..'\246' | '\248'..'\255' as c);
      len = ident (store 0 c) >] ep ->
      let id = get_buff len in current:=InVernac; 
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
  | [< ' ('0'..'9' as c); len = number (store 0 c) >] ep ->
      (("INT", get_buff len), (bp, ep))
  | [< ''"'; len = string bp 0 >] ep ->
      (("STRING", get_buff len), (bp, ep))
  | [< ' ('(' as c);
       t = parser
         | [< ''*'; c; s >] -> (match !current with
				| InVernac -> current := InVernacEsc "(*"
				| _ -> current := InComment "(*"); 
	comment bp c; 
	(match !current with
	| InVernacEsc _ -> add_comment_pp (fnl ()); current := InVernac
	| _ -> ()); 
	next_token s
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
