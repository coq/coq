(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pr_o.cmo pa_macro.cmo" i*) 
(* Add pr_o.cmo to circumvent a useless-warning bug when preprocessed with
 * ast-based camlp4 *)

(*i $Id$ i*)

open Pp
open Util
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

(* Removes a string from a dictionary: returns an equal dictionary
   if the word not present. *)
let ttree_remove ttree str =
  let rec remove tt i =
    if i == String.length str then 
      {node = None; branch = tt.branch}
    else
      let c = str.[i] in
      let br =
        match try Some (CharMap.find c tt.branch) with Not_found -> None with
          | Some tt' ->
              CharMap.add c (remove tt' (i + 1)) (CharMap.remove c tt.branch)
          | None -> tt.branch
      in
      { node = tt.node; branch = br }
  in 
  remove ttree 0


(* Errors occuring while lexing (explained as "Lexer error: ...") *)

type error =
  | Illegal_character
  | Unterminated_comment
  | Unterminated_string
  | Undefined_token
  | Bad_token of string

exception Error of error

let err loc str = Stdpp.raise_with_loc (Util.make_loc loc) (Error str)

let bad_token str = raise (Error (Bad_token str))

(* Lexer conventions on tokens *)

type token_kind =
  | Utf8Token of (utf8_status * int)
  | AsciiChar
  | EmptyStream

let error_unsupported_unicode_character n cs =
  let bp = Stream.count cs in
  err (bp,bp+n) (Bad_token "Unsupported Unicode character")

let error_utf8 cs =
  let bp = Stream.count cs in
  Stream.junk cs; (* consume the char to avoid read it and fail again *)
  err (bp, bp+1) Illegal_character

let njunk n = Util.repeat n Stream.junk

let check_utf8_trailing_byte cs c =
  if Char.code c land 0xC0 <> 0x80 then error_utf8 cs

(* Recognize utf8 blocks (of length less than 4 bytes) *)
(* but don't certify full utf8 compliance (e.g. no emptyness check) *)
let lookup_utf8_tail c cs =
  let c1 = Char.code c in
  if c1 land 0x40 = 0 or c1 land 0x38 = 0x38 then error_utf8 cs 
  else
    let n, unicode =
      if c1 land 0x20 = 0 then
      match Stream.npeek 2 cs with
      | [_;c2] ->
	  check_utf8_trailing_byte cs c2;
	  2, (c1 land 0x1F) lsl 6 + (Char.code c2 land 0x3F)
      | _ -> error_utf8 cs
      else if c1 land 0x10 = 0 then
      match Stream.npeek 3 cs with
      | [_;c2;c3] ->
	  check_utf8_trailing_byte cs c2; check_utf8_trailing_byte cs c3;
	  3, (c1 land 0x0F) lsl 12 + (Char.code c2 land 0x3F) lsl 6 + 
	  (Char.code c3 land 0x3F)
      | _ -> error_utf8 cs
      else match Stream.npeek 4 cs with
      | [_;c2;c3;c4] ->
	  check_utf8_trailing_byte cs c2; check_utf8_trailing_byte cs c3;
	  check_utf8_trailing_byte cs c4; 
	  4, (c1 land 0x07) lsl 18 + (Char.code c2 land 0x3F) lsl 12 +
	  (Char.code c3 land 0x3F) lsl 6 + (Char.code c4 land 0x3F)
      | _ -> error_utf8 cs
    in
    try classify_unicode unicode, n
    with UnsupportedUtf8 -> error_unsupported_unicode_character n cs
	
let lookup_utf8 cs =
  match Stream.peek cs with
    | Some ('\x00'..'\x7F') -> AsciiChar
    | Some ('\x80'..'\xFF' as c) -> Utf8Token (lookup_utf8_tail c cs)
    | None -> EmptyStream

let check_special_token str =
  let rec loop_symb = parser
    | [< ' (' ' | '\n' | '\r' | '\t' | '"') >] -> bad_token str
    | [< _ = Stream.empty >] -> ()
    | [< '_ ; s >] -> loop_symb s
  in
  loop_symb (Stream.of_string str)

let check_ident str =
  let rec loop_id intail = parser
    | [< ' ('a'..'z' | 'A'..'Z' | '_'); s >] ->
        loop_id true s
    | [< ' ('0'..'9' | ''') when intail; s >] ->
        loop_id true s
    | [< s >] ->
	match lookup_utf8 s with
	| Utf8Token (UnicodeLetter, n) -> njunk n s; loop_id true s
	| Utf8Token (UnicodeIdentPart, n) when intail -> njunk n s; loop_id true s
	| EmptyStream -> ()
	| Utf8Token _ | AsciiChar -> bad_token str
  in
  loop_id false (Stream.of_string str)

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

let remove_keyword str = 
  token_tree := ttree_remove !token_tree str

(* Adding a new token (keyword or special token). *)
let add_token (con, str) = match con with
  | "" -> add_keyword str
  | "METAIDENT" | "LEFTQMARK" | "IDENT" | "FIELD" | "INT" | "STRING" | "EOI"
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

(* The string buffering machinery *)

let buff = ref (String.create 80)

let store len x =
  if len >= String.length !buff then
    buff := !buff ^ String.create (String.length !buff);
  !buff.[len] <- x;
  succ len

let rec nstore n len cs =
  if n>0 then nstore (n-1) (store len (Stream.next cs)) cs else len

let get_buff len = String.sub !buff 0 len

(* The classical lexer: idents, numbers, quoted strings, comments *)

let rec ident_tail len = parser
  | [< ' ('a'..'z' | 'A'..'Z' | '0'..'9' | ''' | '_' as c); s >] ->
      ident_tail (store len c) s
  | [< s >] ->
      match lookup_utf8 s with
      | Utf8Token ((UnicodeIdentPart | UnicodeLetter), n) ->
	  ident_tail (nstore n len s) s
      | _ -> len

let rec number len = parser
  | [< ' ('0'..'9' as c); s >] -> number (store len c) s
  | [< >] -> len

let escape len c = store len c

let rec string bp len = parser
  | [< ''"'; esc=(parser [<''"' >] -> true | [< >] -> false); s >] ->
      if esc then string bp (store len '"') s else len
  | [< 'c; s >] -> string bp (store len c) s 
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_string

(* Hook for exporting comment into xml theory files *)
let xml_output_comment = ref (fun _ -> ())
let set_xml_output_comment f = xml_output_comment := f

(* Utilities for comments in beautify *)
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
  if !Flags.xml_export && Buffer.length current > 0 &&
    (!between_com || not(null_comment current_s)) then
      !xml_output_comment current_s;
  (if Flags.do_beautify() && Buffer.length current > 0 &&
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
         | [< '')' >] -> push_string "*)";
         | [< s >] -> real_push_char '*'; comment bp s >] -> ()
  | [< ''"'; s >] ->
      if Flags.do_beautify() then (push_string"\"";comm_string bp2 s)
      else ignore (string bp2 0 s);
      comment bp s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_comment
  | [< 'z; s >] -> real_push_char z; comment bp s

(* Parse a special token, using the [token_tree] *)

(* Peek as much utf-8 lexemes as possible *)
(* and retain the longest valid special token obtained *)
let rec progress_further last nj tt cs =
  try progress_from_byte last nj tt cs (List.nth (Stream.npeek (nj+1) cs) nj)
  with Failure _ -> last

and update_longest_valid_token last nj tt cs =
  match tt.node with
  | Some _ as last' ->
      for i=1 to nj do Stream.junk cs done; 
      progress_further last' 0 tt cs
  | None ->
      progress_further last nj tt cs

(* nr is the number of char peeked since last valid token *)
(* n the number of char in utf8 block *)
and progress_utf8 last nj n c tt cs =
  try
    let tt = CharMap.find c tt.branch in
    if n=1 then
      update_longest_valid_token last (nj+n) tt cs
    else
      match Util.list_skipn (nj+1) (Stream.npeek (nj+n) cs) with
      | l when List.length l = n-1 ->
	 List.iter (check_utf8_trailing_byte cs) l;
	 let tt = List.fold_left (fun tt c -> CharMap.find c tt.branch) tt l in
	 update_longest_valid_token last (nj+n) tt cs
      | _ -> 
	  error_utf8 cs
  with Not_found ->
    last

and progress_from_byte last nj tt cs = function
  (* Utf8 leading byte *)
  | '\x00'..'\x7F' as c -> progress_utf8 last nj 1 c tt cs
  | '\xC0'..'\xDF' as c -> progress_utf8 last nj 2 c tt cs
  | '\xE0'..'\xEF' as c -> progress_utf8 last nj 3 c tt cs
  | '\xF0'..'\xF7' as c -> progress_utf8 last nj 4 c tt cs
  | _ (* '\x80'..\xBF'|'\xF8'..'\xFF' *) ->
      error_utf8 cs

(* Must be a special token *)
let process_chars bp c cs =
  let t = progress_from_byte None (-1) !token_tree cs c in
  let ep = Stream.count cs in
  match t with
    | Some t -> (("", t), (bp, ep))
    | None -> err (bp, ep) Undefined_token

let parse_after_dollar bp =
  parser
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as c); len = ident_tail (store 0 c) >] -> 
      ("METAIDENT", get_buff len)
  | [< s >] ->
      match lookup_utf8 s with
      | Utf8Token (UnicodeLetter, n) ->
	  ("METAIDENT", get_buff (ident_tail (nstore n 0 s) s))
      | AsciiChar | Utf8Token _ | EmptyStream -> fst (process_chars bp '$' s)

(* Parse what follows a dot *)
let parse_after_dot bp c =
  parser
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as c); len = ident_tail (store 0 c) >] ->
      ("FIELD", get_buff len)
  | [< s >] ->
      match lookup_utf8 s with
      | Utf8Token (UnicodeLetter, n) -> 
	  ("FIELD", get_buff (ident_tail (nstore n 0 s) s))
      | AsciiChar | Utf8Token _ | EmptyStream -> 
	  fst (process_chars bp c s)

(* Parse what follows a question mark *)
let parse_after_qmark bp s =
  match Stream.peek s with
    |Some ('a'..'z' | 'A'..'Z' | '_') -> ("LEFTQMARK", "")
    |None -> ("","?")
    | _ ->
	match lookup_utf8 s with
	  | Utf8Token (UnicodeLetter, _) -> ("LEFTQMARK", "")
	  | AsciiChar | Utf8Token _ | EmptyStream -> fst (process_chars bp '?' s)


(* Parse a token in a char stream *)
let rec next_token = parser bp
  | [< '' ' | '\t' | '\n' |'\r' as c; s >] ->
      comm_loc bp; push_char c; next_token s
  | [< ''$'; t = parse_after_dollar bp >] ep ->
      comment_stop bp; (t, (ep, bp))
  | [< ''.' as c; t = parse_after_dot bp c >] ep ->
      comment_stop bp;
      if Flags.do_beautify() & t=("",".") then between_com := true;
      (t, (bp,ep))
  | [< ''?'; s >] ep ->
      let t = parse_after_qmark bp s in comment_stop bp; (t, (ep, bp))
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as c);
       len = ident_tail (store 0 c) >] ep ->
      let id = get_buff len in 
      comment_stop bp;
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
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
  | [< s >] ->
      match lookup_utf8 s with
	| Utf8Token (UnicodeLetter, n) ->
	    let len = ident_tail (nstore n 0 s) s in
	    let id = get_buff len in
	    let ep = Stream.count s in
	    comment_stop bp;
	    (try ("",find_keyword id) with Not_found -> ("IDENT",id)), (bp, ep)
	| AsciiChar | Utf8Token ((UnicodeSymbol | UnicodeIdentPart), _) -> 
	    let t = process_chars bp (Stream.next s) s in
	    comment_stop bp; t
	| EmptyStream ->
	    comment_stop bp; (("EOI", ""), (bp, bp + 1))

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
    | Some loc -> Util.make_loc loc
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

(* The lexer of Coq *)

(* Note: removing a token.
   We do nothing because [remove_token] is called only when removing a grammar
   rule with [Grammar.delete_rule]. The latter command is called only when
   unfreezing the state of the grammar entries (see GRAMMAR summary, file
   env/metasyntax.ml). Therefore, instead of removing tokens one by one,
   we unfreeze the state of the lexer. This restores the behaviour of the
   lexer. B.B. *)

IFDEF CAMLP5 THEN 

let lexer = {
  Token.tok_func = func;
  Token.tok_using = add_token;
  Token.tok_removing = (fun _ -> ());
  Token.tok_match = default_match;
  Token.tok_comm = None;
  Token.tok_text = token_text }

ELSE 

let lexer = {
  Token.func = func;
  Token.using = add_token;
  Token.removing = (fun _ -> ());
  Token.tparse = (fun _ -> None);
  Token.text = token_text }

END

(* Terminal symbols interpretation *)

let is_ident_not_keyword s =
  match s.[0] with
    | 'a'..'z' | 'A'..'Z' | '_' -> not (is_keyword s)
    | _ -> false

let is_number s =
  let rec aux i =
    String.length s = i or 
    match s.[i] with '0'..'9' -> aux (i+1) | _ -> false
  in aux 0

let strip s =
  let len =
    let rec loop i len =
      if i = String.length s then len
      else if s.[i] == ' ' then loop (i + 1) len
      else loop (i + 1) (len + 1)
    in
    loop 0 0
  in
  if len == String.length s then s
  else
    let s' = String.create len in
    let rec loop i i' =
      if i == String.length s then s'
      else if s.[i] == ' ' then loop (i + 1) i'
      else begin s'.[i'] <- s.[i]; loop (i + 1) (i' + 1) end
    in
    loop 0 0

let terminal s =
  let s = strip s in
  if s = "" then failwith "empty token";
  if is_ident_not_keyword s then ("IDENT", s)
  else if is_number s then ("INT", s)
  else ("", s)
