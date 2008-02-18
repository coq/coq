(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)


(*i camlp4use: "pr_o.cmo" i*) 
(* Add pr_o.cmo to circumvent a useless-warning bug when preprocessed with
 * ast-based camlp4 *)

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

type utf8_token =
    Utf8Letter of int | Utf8IdentPart of int | Utf8Symbol | AsciiChar

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
    match unicode land 0x1F000 with
    | 0x0 ->
    begin match unicode with
    (* utf-8 Latin-1 non breaking space U00A0 *)
    | 0x00A0 -> Utf8Letter n
    (* utf-8 Latin-1 symbols U00A1-00BF *)
    | x when 0x00A0 <= x & x <= 0x00BF -> Utf8Symbol
    (* utf-8 Latin-1 letters U00C0-00D6 *)
    | x when 0x00C0 <= x & x <= 0x00D6 -> Utf8Letter n
    (* utf-8 Latin-1 symbol U00D7 *)
    | 0x00D7 -> Utf8Symbol
    (* utf-8 Latin-1 letters U00D8-00F6 *)
    | x when 0x00D8 <= x & x <= 0x00F6 -> Utf8Letter n
    (* utf-8 Latin-1 symbol U00F7 *)
    | 0x00F7 -> Utf8Symbol
    (* utf-8 Latin-1 letters U00F8-00FF *)
    | x when 0x00F8 <= x & x <= 0x00FF -> Utf8Letter n
    (* utf-8 Latin Extended A U0100-017F and Latin Extended B U0180-U0241 *)
    | x when 0x0100 <= x & x <= 0x0241 -> Utf8Letter n
    (* utf-8 Phonetic letters U0250-02AF *)
    | x when 0x0250 <= x & x <= 0x02AF -> Utf8Letter n
    (* utf-8 what do to with diacritics U0300-U036F ? *)
    (* utf-8 Greek letters U0380-03FF *)
    | x when 0x0380 <= x & x <= 0x03FF -> Utf8Letter n
    (* utf-8 Cyrillic letters U0400-0481 *)
    | x when 0x0400 <= x & x <= 0x0481 -> Utf8Letter n
    (* utf-8 Cyrillic symbol U0482 *)
    | 0x0482 -> Utf8Symbol
    (* utf-8 what do to with diacritics U0483-U0489 \ U0487 ? *)
    (* utf-8 Cyrillic letters U048A-U4F9 (Warning: 04CF) *)
    | x when 0x048A <= x & x <= 0x04F9 -> Utf8Letter n
    (* utf-8 Cyrillic supplement letters U0500-U050F *)
    | x when 0x0500 <= x & x <= 0x050F -> Utf8Letter n
    (* utf-8 Hebrew letters U05D0-05EA *)
    | x when 0x05D0 <= x & x <= 0x05EA -> Utf8Letter n
    (* utf-8 Arabic letters U0621-064A *)
    | x when 0x0621 <= x & x <= 0x064A -> Utf8Letter n
    (* utf-8 Arabic supplement letters U0750-076D *)
    | x when 0x0750 <= x & x <= 0x076D -> Utf8Letter n
    | _ -> error_unsupported_unicode_character n cs
    end
    | 0x1000 ->
    begin match unicode with
    (* utf-8 Georgian U10A0-10FF (has holes) *)
    | x when 0x10A0 <= x & x <= 0x10FF -> Utf8Letter n
    (* utf-8 Hangul Jamo U1100-11FF (has holes) *)
    | x when 0x1100 <= x & x <= 0x11FF -> Utf8Letter n
    (* utf-8 Latin additional letters U1E00-1E9B and U1EA0-1EF9 *)
    | x when 0x1E00 <= x & x <= 0x1E9B -> Utf8Letter n
    | x when 0x1EA0 <= x & x <= 0x1EF9 -> Utf8Letter n
    | _ -> error_unsupported_unicode_character n cs
    end
    | 0x2000 ->
    begin match unicode with
    (* utf-8 general punctuation U2080-2089 *)
    (* Hyphens *)
    | x when 0x2010 <= x & x <= 0x2011 -> Utf8Letter n 
    (* Dashes and other symbols *)
    | x when 0x2012 <= x & x <= 0x2027 -> Utf8Symbol
    (* Per mille and per ten thousand signs *)
    | x when 0x2030 <= x & x <= 0x2031 -> Utf8Symbol
    (* Prime letters *)
    | x when 0x2032 <= x & x <= 0x2034 or x = 0x2057 -> Utf8IdentPart n
    (* Miscellaneous punctuation *)
    | x when 0x2039 <= x & x <= 0x2056 -> Utf8Symbol
    | x when 0x2058 <= x & x <= 0x205E -> Utf8Symbol
    (* Invisible mathematical operators *)
    | x when 0x2061 <= x & x <= 0x2063 -> Utf8Symbol

    (* utf-8 subscript U2080-2089 *) 
    | x when 0x2080 <= x & x <= 0x2089 -> Utf8IdentPart n
    (* utf-8 letter-like U2100-214F *)
    | x when 0x2100 <= x & x <= 0x214F -> Utf8Letter n
    (* utf-8 number-forms U2153-2183 *)
    | x when 0x2153 <= x & x <= 0x2183 -> Utf8Symbol
    (* utf-8 arrows A U2190-21FF *)
    (* utf-8 mathematical operators U2200-22FF *)
    (* utf-8 miscellaneous technical U2300-23FF *)
    | x when 0x2190 <= x & x <= 0x23FF -> Utf8Symbol
    (* utf-8 box drawing U2500-257F has ceiling, etc. *)
    (* utf-8 block elements U2580-259F *)
    (* utf-8 geom. shapes U25A0-25FF (has triangles, losange, etc) *)
    (* utf-8 miscellaneous symbols U2600-26FF *)
    | x when 0x2500 <= x & x <= 0x26FF -> Utf8Symbol
    (* utf-8 arrows B U2900-297F *)
    | x when 0x2900 <= x & x <= 0x297F -> Utf8Symbol
    (* utf-8 mathematical operators U2A00-2AFF *)
    | x when 0x2A00 <= x & x <= 0x2AFF -> Utf8Symbol
    (* utf-8 bold symbols U2768-U2775 *)
    | x when 0x2768 <= x & x <= 0x2775 -> Utf8Symbol
    (* utf-8 arrows and brackets U27E0-U27FF *)
    | x when 0x27E0 <= x & x <= 0x27FF -> Utf8Symbol
    (* utf-8 brackets, braces and parentheses *)
    | x when 0x2980 <= x & x <= 0x299F -> Utf8Symbol
    (* utf-8 miscellaneous including double-plus U29F0-U29FF *)
    | x when 0x29F0 <= x & x <= 0x29FF -> Utf8Symbol
    | _ -> error_unsupported_unicode_character n cs
    end
    | _ ->
    begin match unicode with
    (* utf-8 Hiragana U3040-309F and Katakana U30A0-30FF *)
    | x when 0x3040 <= x & x <= 0x30FF -> Utf8Letter n
    (* utf-8 Unified CJK Ideographs U4E00-9FA5 *)
    | x when 0x4E00 <= x & x <= 0x9FA5 -> Utf8Letter n
    (* utf-8 Hangul syllables UAC00-D7AF *)
    | x when 0xAC00 <= x & x <= 0xD7AF -> Utf8Letter n
    (* utf-8 Gothic U10330-1034A *)
    | x when 0x10330 <= x & x <= 0x1034A -> Utf8Letter n
    | _ -> error_unsupported_unicode_character n cs
    end
	
let lookup_utf8 cs =
  match Stream.peek cs with
    | Some ('\x00'..'\x7F') -> Some AsciiChar
    | Some ('\x80'..'\xFF' as c) -> Some (lookup_utf8_tail c cs)
    | None -> None

let check_special_token str =
  let rec loop_symb = parser
    | [< ' (' ' | '\n' | '\r' | '\t' | '"') >] -> bad_token str
    | [< _ = Stream.empty >] -> ()
    | [< '_ ; s >] -> loop_symb s
  in
  loop_symb (Stream.of_string str)

let check_ident str =
  let rec loop_id intail = parser
    | [< ' ('$' | 'a'..'z' | 'A'..'Z' | '_'); s >] ->
        loop_id true s
    | [< ' ('0'..'9' | ''') when intail; s >] ->
        loop_id true s
    | [< s >] ->
	match lookup_utf8 s with
	| Some (Utf8Letter n) -> njunk n s; loop_id true s
	| Some (Utf8IdentPart n) when intail -> njunk n s; loop_id true s
	| Some _ -> bad_token str
	| None -> ()
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

(* Adding a new token (keyword or special token). *)
let add_token (con, str) = match con with
  | "" -> add_keyword str
  | "METAIDENT" | "PATTERNIDENT" | "IDENT" | "FIELD" | "INT" | "STRING" | "EOI"
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
      | Some (Utf8IdentPart n | Utf8Letter n) ->
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
  if !Flags.xml_export && Buffer.length current > 0 &&
    (!between_com || not(null_comment current_s)) then
      !xml_output_comment current_s;
  (if Flags.do_translate() && Buffer.length current > 0 &&
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
      if Flags.do_translate() then (push_string"\"";comm_string bp2 s)
      else ignore (string bp2 0 s);
      comment bp s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_comment
  | [< 'z; s >] -> real_push_char z; comment bp s

(* Parse a special token, using the [token_tree] *)

(* Peek as much utf-8 lexemes as possible *)
(* then look if a special token is obtained *)
let rec special tt cs =
  match Stream.peek cs with
    | Some c -> progress_from_byte 0 tt cs c
    | None -> tt.node

  (* nr is the number of char peeked; n the number of char in utf8 block *)
and progress_utf8 nr n c tt cs =
  try
    let tt = CharMap.find c tt.branch in
    let tt =
      if n=1 then tt else
	match Stream.npeek (n-nr) cs with
	| l when List.length l = n-nr ->
	    let l = Util.list_skipn (1-nr) l in
	    List.iter (check_utf8_trailing_byte cs) l;
	    List.fold_left (fun tt c -> CharMap.find c tt.branch) tt l
	| _ -> 
	    error_utf8 cs
    in
    for i=1 to n-nr do Stream.junk cs done;
    special tt cs
  with Not_found ->
    tt.node

and progress_from_byte nr tt cs = function
  (* Utf8 leading byte *)
  | '\x00'..'\x7F' as c -> progress_utf8 nr 1 c tt cs
  | '\xC0'..'\xDF' as c -> progress_utf8 nr 2 c tt cs
  | '\xE0'..'\xEF' as c -> progress_utf8 nr 3 c tt cs
  | '\xF0'..'\xF7' as c -> progress_utf8 nr 4 c tt cs
  | _ (* '\x80'..\xBF'|'\xF8'..'\xFF' *) ->
      error_utf8 cs

(* Must be a special token *)
let process_chars bp c cs =
  let t = progress_from_byte 1 !token_tree cs c in
  let ep = Stream.count cs in
  match t with
    | Some t -> (("", t), (bp, ep))
    | None -> err (bp, ep) Undefined_token

(* Parse what follows a dot/question mark *)
let parse_after_dot bp c =
  let constructor = if c = '?' then "PATTERNIDENT" else "FIELD" in
  parser
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as c); len = ident_tail (store 0 c) >] ->
      (constructor, get_buff len)
  | [< s >] ->
      match lookup_utf8 s with
      | Some (Utf8Letter n) -> 
	  (constructor, get_buff (ident_tail (nstore n 0 s) s))
      | Some (Utf8IdentPart _ | AsciiChar | Utf8Symbol) | None -> 
	  fst (process_chars bp c s)

(* Parse a token in a char stream *)
let rec next_token = parser bp
  | [< '' ' | '\t' | '\n' |'\r' as c; s >] ->
      comm_loc bp; push_char c; next_token s
  | [< ''$'; len = ident_tail (store 0 '$') >] ep -> 
      comment_stop bp;
      (("METAIDENT", get_buff len), (bp,ep))
  | [< ' ('.' | '?') as c; t = parse_after_dot bp c >] ep ->
      comment_stop bp;
      if Flags.do_translate() & t=("",".") then between_com := true;
      (t, (bp,ep))
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
	| Some (Utf8Letter n) ->
	    let len = ident_tail (nstore n 0 s) s in
	    let id = get_buff len in
	    let ep = Stream.count s in
	    comment_stop bp;
	    (try ("",find_keyword id) with Not_found -> ("IDENT",id)), (bp, ep)
	| Some (Utf8Symbol | AsciiChar | Utf8IdentPart _) -> 
	    let t = process_chars bp (Stream.next s) s in
	    comment_stop bp; t
	| None ->
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

let tparse (p_con, p_prm) =
  None
  (*i was
  if p_prm = "" then
    (parser [< '(con, prm) when con = p_con >] -> prm)
  else
    (parser [< '(con, prm) when con = p_con && prm = p_prm >] -> prm)
  i*)

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
