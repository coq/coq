(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
  let rec loop_symb = parser
    | [< ' (' ' | '\n' | '\r' | '\t' | '"') >] -> bad_token str
    | [< _ = Stream.empty >] -> ()
    | [< '_ ; s >] -> loop_symb s
  in
  loop_symb (Stream.of_string str)

let check_ident str =
  let first_letter = function
      (''' | '0'..'9') -> false
    | _ -> true in
  let rec loop_id = parser
    | [< ' ('$' | 'a'..'z' | 'A'..'Z' | '0'..'9' | ''' | '_'); s >] ->
        loop_id s
    (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
    | [< ' ('\206' | '\207'); ' ('\128'..'\191'); s >] -> loop_id s
    | [< ''\226'; 'c2; 'c3; s >] ->
	  (match c2, c3 with
	      (* utf8 letter-like unicode 2100-214F *) 
	    | (('\132', '\128'..'\191') | ('\133', '\128'..'\143')) ->
                loop_id s 
		(* utf8 symbols (see [parse_226_tail]) *)
	    | (('\134'..'\143' | '\152'..'\155' | '\159'
               | '\164'..'\171'),_) ->
		bad_token str
	    | _ -> (* default to iso 8859-1 "â" *)
		if !Options.v7 then loop_id [< 'c2; 'c3; s >]
                else bad_token str)
	(* iso 8859-1 accentuated letters *)
    | [< ' ('\192'..'\214' | '\216'..'\246' | '\248'..'\255'); s >] ->
        if !Options.v7 then loop_id s else bad_token str
    | [< _ = Stream.empty >] -> ()
    | [< >] -> bad_token str
  in
  if String.length str > 0 && first_letter str.[0] then
    loop_id (Stream.of_string str)
  else
    bad_token str

let check_keyword str =
  try check_special_token str
  with Error _ -> check_ident str

(* Keyword and symbol dictionary *)
let token_tree = ref empty_ttree

let find_keyword s = ttree_find !token_tree s

let is_keyword s = 
  try let _ = ttree_find !token_tree s in true with Not_found -> false

let add_keyword str =
  check_keyword str;
  token_tree := ttree_add !token_tree str

(* Adding a new token (keyword or special token). *)
let add_token (con, str) = match con with
  | "" -> add_keyword str
  | "METAIDENT" | "IDENT" | "FIELD" | "INT" | "STRING" | "EOI"
      -> ()
  | _ ->
      raise (Token.Error ("\
the constructor \"" ^ con ^ "\" is not recognized by Lexer"))


(* Freeze and unfreeze the state of the lexer *)
type frozen_t = ttree

let freeze () = !token_tree

let unfreeze tt =
  token_tree := tt

let init () =
  unfreeze empty_ttree

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

let rec ident_tail len strm =
  if !Options.v7 then
    match strm with parser
      | [< ' ('a'..'z' | 'A'..'Z' | '0'..'9' | ''' | '_' | '@' as c); s >] ->
          ident_tail (store len c) s
      (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
      | [< ' ('\206' | '\207' as c1); ' ('\128'..'\191' as c2) ; s >] ->
          ident_tail (store (store len c1) c2) s
      (* iso 8859-1 accentuated letters *)
      | [< ' ('\192'..'\214' | '\216'..'\246' | '\248'..'\255' as c); s >] -> 
          ident_tail (store len c) s
      | [< >] -> len
  else
    match strm with parser
      | [< ' ('a'..'z' | 'A'..'Z' | '0'..'9' | ''' | '_' as c); s >] ->
          ident_tail (store len c) s
      (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
      | [< ' ('\206' | '\207' as c1); ' ('\128'..'\191' as c2) ; s >] ->
          ident_tail (store (store len c1) c2) s
      | [< >] -> len


let rec number len = parser
  | [< ' ('0'..'9' as c); s >] -> number (store len c) s
  | [< >] -> len

let escape len c = store len c

let rec string_v8 bp len = parser
  | [< ''"'; esc=(parser [<''"' >] -> true | [< >] -> false); s >] ->
      if esc then string_v8 bp (store len '"') s else len
  | [< 'c; s >] -> string_v8 bp (store len c) s 
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_string

let rec string_v7 bp len = parser
  | [< ''"' >] -> len
  | [< ''\\'; c = (parser [< ' ('"' | '\\' as c) >] -> c | [< >] -> '\\'); s >]
     -> string_v7 bp (escape len c) s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_string
  | [< 'c; s >] -> string_v7 bp (store len c) s 

let string bp len s =
  if !Options.v7 then string_v7 bp len s else string_v8 bp len s

(* Hook for exporting comment into xml theory files *)
let xml_output_comment = ref (fun _ -> ())
let set_xml_output_comment f = xml_output_comment := f

(* Utilities for comment translation *)
let comment_begin = ref None
let comm_loc bp = if !comment_begin=None then comment_begin := Some bp

let current = Buffer.create 8192
let between_com = ref true

type com_state = int option * string * bool
let restore_com_state (o,s,b) =
  comment_begin := o; 
  Buffer.clear current; Buffer.add_string current s; 
  between_com := b
let dflt_com = (None,"",true)
let com_state () =
  let s = (!comment_begin, Buffer.contents current, !between_com) in
  restore_com_state dflt_com; s

let real_push_char c = Buffer.add_char current c

(* Add a char if it is between two commands, if it is a newline or
   if the last char is not a space itself. *)
let push_char c =
  if
    !between_com || List.mem c ['\n';'\r'] ||
    (List.mem c [' ';'\t']&&
     (Buffer.length current = 0 ||
      not (let s = Buffer.contents current in
	   List.mem s.[String.length s - 1] [' ';'\t';'\n';'\r'])))
  then
    real_push_char c

let push_string s = Buffer.add_string current s

let null_comment s =
  let rec null i =
    i<0 || (List.mem s.[i] [' ';'\t';'\n';'\r'] && null (i-1)) in
  null (String.length s - 1)

let comment_stop ep =
  let current_s = Buffer.contents current in
  if !Options.xml_export && Buffer.length current > 0 &&
    (!between_com || not(null_comment current_s)) then
      !xml_output_comment current_s;
  (if Options.do_translate() && Buffer.length current > 0 &&
    (!between_com || not(null_comment current_s)) then
    let bp = match !comment_begin with
        Some bp -> bp
      | None ->
          msgerrnl(str"No begin location for comment '"++str current_s ++str"' ending at  "++int ep);
          ep-1 in
    Pp.comments := ((bp,ep),current_s) :: !Pp.comments);
  Buffer.clear current;
  comment_begin := None;
  between_com := false

(* Does not unescape!!! *)
let rec comm_string bp = parser
  | [< ''"' >] -> push_string "\""
  | [< ''\\'; _ =
           (parser [< ' ('"' | '\\' as c) >] ->
             if c='"' then real_push_char c;
             real_push_char c
                 | [< >] -> real_push_char '\\'); s >]
     -> comm_string bp s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_string
  | [< 'c; s >] -> real_push_char c; comm_string bp s 

let rec comment bp = parser bp2
  | [< ''(';
       _ = (parser
              | [< ''*'; s >] -> push_string "(*"; comment bp s
              | [< >] -> push_string "(" ); 
       s >] -> comment bp s
  | [< ''*';
       _ = parser
         | [< '')' >] ep -> push_string "*)";
         | [< s >] -> real_push_char '*'; comment bp s >] -> ()
  | [< ''"'; s >] ->
      if Options.do_translate() then (push_string"\"";comm_string bp2 s)
      else ignore (string bp2 0 s);
      comment bp s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_comment
  | [< '_ as z; s >] ep -> real_push_char z; comment bp s

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
      len = ident_tail (store (store (store 0 '\226') c2) c3) >] ->
      TokIdent (get_buff len) 
  | [< ''\133' as c2; ' ('\128'..'\143' as c3);
      (* utf8 letter-like unicode 2100-214F *)
      len = ident_tail (store (store (store 0 '\226') c2) c3) >] ->
      TokIdent (get_buff len) 
  | [< ' ('\134'..'\143' | '\152'..'\155' | '\159' 
         | '\164'..'\171' as c2); 'c3;
      (* utf8 arrows A unicode 2190-21FF *)
      (* utf8 mathematical operators unicode 2200-22FF *)
      (* utf8 miscellaneous technical unicode 2300-23FF *)
      (* utf8 miscellaneous symbols unicode 2600-26FF *)
      (* utf8 Miscellaneous Mathematical Symbols-A unicode 27C0-27DF *)
      (* utf8 Supplemental Arrows-A unicode 27E0-27FF *)
      (* utf8 Supplemental Arrows-B unicode 2900-297F *)
      (* utf8 Miscellaneous Mathematical Symbols-B unicode 2980-29FF *)
      (* utf8 mathematical operators unicode 2A00-2AFF *)
      t = special (progress_special c3 (progress_special c2 
	(progress_special '\226' tk))) >] ->
      TokSymbol t
  | [< len = ident_tail (store 0 '\226') >] ->
      TokIdent (get_buff len)


(* Parse what follows a dot *)
let parse_after_dot bp c strm =
  if !Options.v7 then 
    match strm with parser
	 | [< ' ('_' | 'a'..'z' | 'A'..'Z' as c);
              len = ident_tail (store 0 c) >] ->
	     ("FIELD", get_buff len)
	 (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
	 | [< ' ('\206' | '\207' as c1); ' ('\128'..'\191' as c2); 
	   len = ident_tail (store (store 0 c1) c2) >] ->
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
	   len = ident_tail (store 0 c) >] ->
	     ("FIELD", get_buff len)
	 | [< (t,_) = process_chars bp c >] -> t
  else
    match strm with parser
	 | [< ' ('a'..'z' | 'A'..'Z' | '_' as c);
              len = ident_tail (store 0 c) >] ->
	     ("FIELD", get_buff len)
	 (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
	 | [< ' ('\206' | '\207' as c1); ' ('\128'..'\191' as c2); 
	   len = ident_tail (store (store 0 c1) c2) >] ->
	     ("FIELD", get_buff len)
         (* utf-8 mathematical symbols have format E2 xx xx [E2=226] *)
	 | [< ''\226' as c1; t = parse_226_tail 
	     (progress_special '.' (Some !token_tree)) >] ep ->
	     (match t with
	       | TokSymbol (Some t) -> ("", t)
	       | TokSymbol None -> err (bp, ep) Undefined_token
	       | TokIdent t -> ("FIELD", t))
	 | [< (t,_) = process_chars bp c >] -> t


(* Parse a token in a char stream *)

let rec next_token = parser bp
  | [< '' ' | '\t' | '\n' |'\r' as c; s >] ep ->
      comm_loc bp; push_char c; next_token s
  | [< ''$'; len = ident_tail (store 0 '$') >] ep -> 
      comment_stop bp;
      (("METAIDENT", get_buff len), (bp,ep))
  | [< ''.' as c; t = parse_after_dot bp c >] ep ->
      comment_stop bp;
      if !Options.v7 & t=("",".") then between_com := true;
      (t, (bp,ep))
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as c);
       len = ident_tail (store 0 c) >] ep ->
      let id = get_buff len in 
      comment_stop bp;
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
  (* Greek utf-8 letters [CE80-CEBF and CF80-CFBF] (CE=206; BF=191) *)
  | [< ' ('\206' | '\207' as c1); ' ('\128'..'\191' as c2); 
	   len = ident_tail (store (store 0 c1) c2) >] ep ->
      let id = get_buff len in
      comment_stop bp;
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
  (* utf-8 mathematical symbols have format E2 xx xx [E2=226] *)
  | [< ''\226' as c1; t = parse_226_tail (Some !token_tree) >] ep ->
      comment_stop bp;
      (match t with
	| TokSymbol (Some t) -> ("", t), (bp, ep)
	| TokSymbol None -> err (bp, ep) Undefined_token
	| TokIdent id ->
	    (try ("", find_keyword id) with Not_found -> ("IDENT", id)),
	    (bp, ep))
  (* iso 8859-1 accentuated letters *)
  | [< ' ('\192'..'\214' | '\216'..'\246' | '\248'..'\255' as c) ; s >] ->
      if !Options.v7 then
	begin
	  match s with parser
	      [< len = ident_tail (store 0 c) >] ep ->
		let id = get_buff len in
		comment_stop bp;
		(try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
	end
      else
	begin
	  match s with parser
	      [< t = process_chars bp c >] -> comment_stop bp; t
	end
  | [< ' ('0'..'9' as c); len = number (store 0 c) >] ep ->
      comment_stop bp;
      (("INT", get_buff len), (bp, ep))
  | [< ''\"'; len = string bp 0 >] ep ->
      comment_stop bp;
      (("STRING", get_buff len), (bp, ep))
  | [< ' ('(' as c);
      t = parser
        | [< ''*'; s >] ->
            comm_loc bp;
            push_string "(*";
	    comment bp s;
	    next_token s
        | [< t = process_chars bp c >] -> comment_stop bp; t >] ->
      t
  | [< 'c; t = process_chars bp c >] -> comment_stop bp; t
  | [< _ = Stream.empty >] -> comment_stop bp; (("EOI", ""), (bp, bp + 1))

(* Location table system for creating tables associating a token count
   to its location in a char stream (the source) *)

let locerr () = invalid_arg "Lexer: location function"

let tsz = 256   (* up to 2^29 entries on a 32-bit machine, 2^61 on 64-bit *)

let loct_create () = ref [| [| |] |]

let loct_func loct i =
  match
    if i < 0 || i/tsz >= Array.length !loct then None
    else if !loct.(i/tsz) = [| |] then None
    else !loct.(i/tsz).(i mod tsz)
  with
    | Some loc -> loc
    | _ -> locerr ()

let loct_add loct i loc =
  while i/tsz >= Array.length !loct do
    let new_tmax = Array.length !loct * 2 in
    let new_loct = Array.make new_tmax [| |] in
    Array.blit !loct 0 new_loct 0 (Array.length !loct);
    loct := new_loct;
  done;
  if !loct.(i/tsz) = [| |] then !loct.(i/tsz) <- Array.make tsz None;
  !loct.(i/tsz).(i mod tsz) <- Some loc

let current_location_table = ref (ref [| [| |] |])

let location_function n =
  loct_func !current_location_table n

let func cs =
  let loct = loct_create () in
  let ts =
    Stream.from
      (fun i ->
         let (tok, loc) = next_token cs in
	 loct_add loct i loc; Some tok)
  in
  current_location_table := loct;
  (ts, loct_func loct)

type location_table = (int * int) option array array ref
let location_table () = !current_location_table
let restore_location_table t = current_location_table := t

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
