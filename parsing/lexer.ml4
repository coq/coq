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
    (* utf-8 Greek letters U0380-03FF *)
    | [< ' ('\xCE' | '\xCF'); ' ('\x80'..'\xBF'); s >] -> loop_id s
    | [< ''\xE2'; 'c2; 'c3; s >] ->
	  (match c2, c3 with
	      (* utf-8 letter-like U2100-214F *)
	    | ( ('\x84', '\x80'..'\xBF')
	      | ('\x85', '\x80'..'\x8F')
	      (* utf-8 subscript U2080-2089 *) 
	      | ('\x82', '\x80'..'\x89')) ->
                loop_id s 
	      (* utf-8 symbols (see [parse_226_tail]) *)
	    | (('\x86'..'\x8F' | '\x94'..'\x9B'
               | '\xA4'..'\xA5' | '\xA8'..'\xAB'),_) ->
		bad_token str
	    | _ -> 
		bad_token str)
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
let err loc str = Stdpp.raise_with_loc (Util.make_loc loc) (Error str)

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

let rec ident_tail len = parser
  | [< ' ('a'..'z' | 'A'..'Z' | '0'..'9' | ''' | '_' as c); s >] ->
      ident_tail (store len c) s
  (* utf-8 Greek letters U0380-03FF *)
  | [< ' ('\xCE' | '\xCF' as c1); ' ('\x80'..'\xBF' as c2) ; s >] ->
      ident_tail (store (store len c1) c2) s
  | [< s >] ->
      match Stream.peek s with
      | Some '\xE2' -> 
	  (match List.tl (Stream.npeek 3 s) with
	    (* utf-8 subscript U2080-2089 *) 
	  | ['\x82' as c2; ('\x80'..'\x89' as c3)]
	    (* utf-8 letter-like U2100-214F part 1 *)
	  | ['\x84' as c2; ('\x80'..'\xBF' as c3)]
	    (* utf-8 letter-like U2100-214F part 2 *)
	  | ['\x85' as c2; ('\x80'..'\x8F' as c3)] ->
	    Stream.junk s; Stream.junk s; Stream.junk s;
	    ident_tail (store (store (store len '\xE2') c2) c3) s
	  | _ -> len)
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
         | [< '')' >] -> push_string "*)";
         | [< s >] -> real_push_char '*'; comment bp s >] -> ()
  | [< ''"'; s >] ->
      if Options.do_translate() then (push_string"\"";comm_string bp2 s)
      else ignore (string bp2 0 s);
      comment bp s
  | [< _ = Stream.empty >] ep -> err (bp, ep) Unterminated_comment
  | [< 'z; s >] -> real_push_char z; comment bp s

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

(* 1110xxxx 10yyyyzz 10zztttt utf-8 codes for xxxx=0010 *)
let parse_226_tail tk = parser
  | [< ''\x82' as c2; ' ('\x80'..'\x89' as c3);
      (* utf-8 subscript U2080-2089 *) 
      len = ident_tail (store (store (store 0 '\xE2') c2) c3) >] ->
      TokIdent (get_buff len) 
  | [< ''\x84' as c2; ' ('\x80'..'\xBF' as c3);
      (* utf-8 letter-like U2100-214F part 1 *)
      len = ident_tail (store (store (store 0 '\xE2') c2) c3) >] ->
      TokIdent (get_buff len) 
  | [< ''\x85' as c2; ' ('\x80'..'\x8F' as c3);
      (* utf-8 letter-like U2100-214F part 2 *)
      len = ident_tail (store (store (store 0 '\xE2') c2) c3) >] ->
      TokIdent (get_buff len) 
  | [< ' ('\x86'..'\x8F' | '\x94'..'\x9B' | '\xA4'..'\xA5' 
         | '\xA8'..'\xAB' as c2); 'c3;
      (* utf-8 arrows A U2190-21FF *)
      (* utf-8 mathematical operators U2200-22FF *)
      (* utf-8 miscellaneous technical U2300-23FF *)
      (* utf-8 box drawing U2500-257F has ceiling, etc. *)
      (* utf-8 block elements U2580-259F *)
      (* utf-8 geom. shapes U25A0-25FF (has triangles, losange, etc) *)
      (* utf-8 miscellaneous symbols U2600-26FF *)
      (* utf-8 arrows B U2900-297F *)
      (* utf-8 mathematical operators U2A00-2AFF *)
      t = special (progress_special c3 (progress_special c2 
	(progress_special '\xE2' tk))) >] ->
      TokSymbol t
  | [< '_; '_ >] ->
      (* Unsupported utf-8 code *)
      TokSymbol None

(* Parse what follows a dot *)
let parse_after_dot bp c = parser
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as c);
    len = ident_tail (store 0 c) >] ->
      ("FIELD", get_buff len)
  (* utf-8 Greek letters U0380-03FF *)
  | [< ' ('\xCE' | '\xCF' as c1); ' ('\x80'..'\xBF' as c2); 
    len = ident_tail (store (store 0 c1) c2) >] ->
      ("FIELD", get_buff len)
  (* utf-8 mathematical symbols have format E2 xx xx [E2=226] *)
  | [< ''\xE2'; t = parse_226_tail 
      (progress_special '.' (Some !token_tree)) >] ep ->
      (match t with
	| TokSymbol (Some t) -> ("", t)
	| TokSymbol None -> err (bp, ep) Undefined_token
	| TokIdent t -> ("FIELD", t))
  | [< (t,_) = process_chars bp c >] -> t


(* Parse a token in a char stream *)

let rec next_token = parser bp
  | [< '' ' | '\t' | '\n' |'\r' as c; s >] ->
      comm_loc bp; push_char c; next_token s
  | [< ''$'; len = ident_tail (store 0 '$') >] ep -> 
      comment_stop bp;
      (("METAIDENT", get_buff len), (bp,ep))
  | [< ''.' as c; t = parse_after_dot bp c >] ep ->
      comment_stop bp;
      (t, (bp,ep))
  | [< ' ('a'..'z' | 'A'..'Z' | '_' as c);
       len = ident_tail (store 0 c) >] ep ->
      let id = get_buff len in 
      comment_stop bp;
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
  (* utf-8 Greek letters U0380-03FF [CE80-CEBF and CF80-CFBF] *)
  | [< ' ('\xCE' | '\xCF' as c1); ' ('\x80'..'\xBF' as c2); 
	   len = ident_tail (store (store 0 c1) c2) >] ep ->
      let id = get_buff len in
      comment_stop bp;
      (try ("", find_keyword id) with Not_found -> ("IDENT", id)), (bp, ep)
  (* utf-8 mathematical symbols have format E2 xx xx [E2=226] *)
  | [< ''\xE2'; t = parse_226_tail (Some !token_tree) >] ep ->
      comment_stop bp;
      (match t with
	| TokSymbol (Some t) -> ("", t), (bp, ep)
	| TokSymbol None -> err (bp, ep) Undefined_token
	| TokIdent id ->
	    (try ("", find_keyword id) with Not_found -> ("IDENT", id)),
	    (bp, ep))
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
  match s.[0] with
    | '0'..'9' -> true
    | _ -> false

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
