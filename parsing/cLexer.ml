(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Tok
open Gramlib

(* Dictionaries: trees annotated with string options, each node being a map
   from chars to dictionaries (the subtrees). A trie, in other words. *)

module CharOrd = struct type t = char let compare : char -> char -> int = compare end
module CharMap = Map.Make (CharOrd)

type starts_quotation = NoQuotation | Quotation

type ttree = {
  node : (string * starts_quotation) option;
  branch : ttree CharMap.t;
}

let empty_ttree = { node = None; branch = CharMap.empty }

let ttree_add ttree (str,quot) =
  let rec insert tt i =
    if i == String.length str then
      {node = Some (str,quot); branch = tt.branch}
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
    if i == String.length str then tt
    else proc_rec (CharMap.find str.[i] tt.branch) (i+1)
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

let ttree_elements ttree =
  let rec elts tt accu =
    let accu = match tt.node with
    | None -> accu
    | Some (s,_) -> CString.Set.add s accu
    in
    CharMap.fold (fun _ tt accu -> elts tt accu) tt.branch accu
  in
  elts ttree CString.Set.empty

(* Errors occurring while lexing (explained as "Lexer error: ...") *)

module Error = struct

  type t =
    | Illegal_character
    | Unterminated_comment
    | Unterminated_string
    | Undefined_token
    | Bad_token of string

  exception E of t

  let to_string x =
    "Syntax Error: Lexer: " ^
      (match x with
         | Illegal_character -> "Illegal character"
         | Unterminated_comment -> "Unterminated comment"
         | Unterminated_string -> "Unterminated string"
         | Undefined_token -> "Undefined token"
         | Bad_token tok -> Format.sprintf "Bad token %S" tok)

end
open Error

let err loc str = Loc.raise ~loc (Error.E str)

let bad_token str = raise (Error.E (Bad_token str))

(* Update a loc without allocating an intermediate pair *)
let set_loc_pos loc bp ep =
  Ploc.sub loc (bp - loc.Loc.bp) (ep - bp)

(* Increase line number by 1 and update position of beginning of line *)
let bump_loc_line loc bol_pos =
  Loc.{ loc with
        line_nb      = loc.line_nb + 1;
        line_nb_last = loc.line_nb + 1;
        bol_pos;
        bol_pos_last = bol_pos;
      }

(* Same as [bump_loc_line], but for the last line in location *)
(* For an obscure reason, camlp5 does not give an easy way to set line_nb_stop,
   so we have to resort to a hack merging two locations. *)
(* Warning: [bump_loc_line_last] changes the end position. You may need to call
   [set_loc_pos] to fix it. *)
let bump_loc_line_last loc bol_pos =
  let open Loc in
  let loc' = { loc with
               line_nb      = loc.line_nb_last + 1;
               line_nb_last = loc.line_nb_last + 1;
               bol_pos;
               bol_pos_last = bol_pos;
               bp = loc.bp + 1;
               ep = loc.ep + 1;
             } in
  Loc.merge loc loc'

(* For some reason, the [Ploc.after] function of Camlp5 does not update line
   numbers, so we define our own function that does it. *)
let after loc =
  Loc.{ loc with
        line_nb = loc.line_nb_last;
        bol_pos = loc.bol_pos_last;
        bp      = loc.ep;
      }

(** Lexer conventions on tokens *)

type token_kind =
  | Utf8Token of (Unicode.status * int)
  | AsciiChar
  | EmptyStream

let error_utf8 loc cs =
  let bp = Stream.count cs in
  Stream.junk cs; (* consume the char to avoid read it and fail again *)
  let loc = set_loc_pos loc bp (bp+1) in
  err loc Illegal_character

let utf8_char_size loc cs = function
  (* Utf8 leading byte *)
  | '\x00'..'\x7F' -> 1
  | '\xC0'..'\xDF' -> 2
  | '\xE0'..'\xEF' -> 3
  | '\xF0'..'\xF7' -> 4
  | _ (* '\x80'..\xBF'|'\xF8'..'\xFF' *) -> error_utf8 loc cs

let njunk n = Util.repeat n Stream.junk

let check_utf8_trailing_byte loc cs c =
  if not (Int.equal (Char.code c land 0xC0) 0x80) then error_utf8 loc cs

(* Recognize utf8 blocks (of length less than 4 bytes) *)
(* but don't certify full utf8 compliance (e.g. no emptyness check) *)
let lookup_utf8_tail loc c cs =
  let c1 = Char.code c in
  if Int.equal (c1 land 0x40) 0 || Int.equal (c1 land 0x38) 0x38 then error_utf8 loc cs
  else
    let n, unicode =
      if Int.equal (c1 land 0x20) 0 then
      match Stream.npeek 2 cs with
      | [_;c2] ->
          check_utf8_trailing_byte loc cs c2;
          2, (c1 land 0x1F) lsl 6 + (Char.code c2 land 0x3F)
      | _ -> error_utf8 loc cs
      else if Int.equal (c1 land 0x10) 0 then
      match Stream.npeek 3 cs with
      | [_;c2;c3] ->
          check_utf8_trailing_byte loc cs c2;
	  check_utf8_trailing_byte loc cs c3;
          3, (c1 land 0x0F) lsl 12 + (Char.code c2 land 0x3F) lsl 6 +
          (Char.code c3 land 0x3F)
      | _ -> error_utf8 loc cs
      else match Stream.npeek 4 cs with
      | [_;c2;c3;c4] ->
          check_utf8_trailing_byte loc cs c2;
	  check_utf8_trailing_byte loc cs c3;
          check_utf8_trailing_byte loc cs c4;
          4, (c1 land 0x07) lsl 18 + (Char.code c2 land 0x3F) lsl 12 +
          (Char.code c3 land 0x3F) lsl 6 + (Char.code c4 land 0x3F)
      | _ -> error_utf8 loc cs
    in
    Utf8Token (Unicode.classify unicode, n)

let lookup_utf8 loc cs =
  match Stream.peek cs with
    | Some ('\x00'..'\x7F') -> AsciiChar
    | Some ('\x80'..'\xFF' as c) -> lookup_utf8_tail loc c cs
    | None -> EmptyStream

let unlocated f x = f x
  (** FIXME: should we still unloc the exception? *)
(*   try f x with Loc.Exc_located (_, exc) -> raise exc *)

let check_keyword str =
  let rec loop_symb s = match Stream.peek s with
    | Some (' ' | '\n' | '\r' | '\t' | '"') ->
        Stream.junk s;
        bad_token str
    | _ ->
        match unlocated lookup_utf8 Ploc.dummy s with
        | Utf8Token (_,n) -> njunk n s; loop_symb s
        | AsciiChar -> Stream.junk s; loop_symb s
        | EmptyStream -> ()
  in
  loop_symb (Stream.of_string str)

let check_ident str =
  let rec loop_id intail s = match Stream.peek s with
    | Some ('a'..'z' | 'A'..'Z' | '_') ->
        Stream.junk s;
        loop_id true s
    | Some ('0'..'9' | '\'') when intail ->
        Stream.junk s;
        loop_id true s
    | _ ->
        match unlocated lookup_utf8 Ploc.dummy s with
        | Utf8Token (st, n) when not intail && Unicode.is_valid_ident_initial st -> njunk n s; loop_id true s
        | Utf8Token (st, n) when intail && Unicode.is_valid_ident_trailing st ->
          njunk n s;
          loop_id true s
        | EmptyStream -> ()
        | Utf8Token _ | AsciiChar -> bad_token str
  in
  loop_id false (Stream.of_string str)

let is_ident str =
  try let _ = check_ident str in true with Error.E _ -> false

(* Keyword and symbol dictionary *)
let token_tree = ref empty_ttree

let is_keyword s =
  try match (ttree_find !token_tree s).node with None -> false | Some _ -> true
  with Not_found -> false

let add_keyword ?(quotation=NoQuotation) str =
  if not (is_keyword str) then
    begin
      check_keyword str;
      token_tree := ttree_add !token_tree (str,quotation)
    end

let remove_keyword str =
  token_tree := ttree_remove !token_tree str

let keywords () = ttree_elements !token_tree

(* Freeze and unfreeze the state of the lexer *)
type keyword_state = ttree

let get_keyword_state () = !token_tree
let set_keyword_state tt = (token_tree := tt)

(* The string buffering machinery *)

let buff = ref (Bytes.create 80)

let store len x =
  let open Bytes in
  if len >= length !buff then
    buff := cat !buff (create (length !buff));
  set !buff len x;
  succ len

let rec nstore n len cs =
  if n>0 then nstore (n-1) (store len (Stream.next cs)) cs else len

let get_buff len = Bytes.sub_string !buff 0 len

(* The classical lexer: idents, numbers, quoted strings, comments *)

let warn_unrecognized_unicode =
  CWarnings.create ~name:"unrecognized-unicode" ~category:"parsing"
         (fun (u,id) ->
          strbrk (Printf.sprintf "Not considering unicode character \"%s\" of unknown \
                                  lexical status as part of identifier \"%s\"." u id))

let rec ident_tail loc len s = match Stream.peek s with
  | Some ('a'..'z' | 'A'..'Z' | '0'..'9' | '\'' | '_' as c) ->
      Stream.junk s;
      ident_tail loc (store len c) s
  | _ ->
      match lookup_utf8 loc s with
      | Utf8Token (st, n) when Unicode.is_valid_ident_trailing st ->
          ident_tail loc (nstore n len s) s
      | Utf8Token (st, n) when Unicode.is_unknown st ->
          let id = get_buff len in
          let u = String.concat "" (List.map (String.make 1) (Stream.npeek n s)) in
          warn_unrecognized_unicode ~loc (u,id); len
      | _ -> len

let warn_comment_terminator_in_string =
  CWarnings.create ~name:"comment-terminator-in-string" ~category:"parsing"
         (fun () ->
          (strbrk
             "Not interpreting \"*)\" as the end of current \
              non-terminated comment because it occurs in a \
              non-terminated string of the comment."))

(* If the string being lexed is in a comment, [comm_level] is Some i with i the
   current level of comments nesting. Otherwise, [comm_level] is None. *)
let rec string loc ~comm_level bp len s = match Stream.peek s with
  | Some '"' ->
      Stream.junk s;
      let esc =
        match Stream.peek s with
          Some '"' -> Stream.junk s; true
        | _ -> false
      in
      if esc then string loc ~comm_level bp (store len '"') s else (loc, len)
  | Some '(' ->
      Stream.junk s;
      (fun s -> match Stream.peek s with
      | Some '*' ->
        Stream.junk s;
        let comm_level = Option.map succ comm_level in
            string loc ~comm_level
              bp (store (store len '(') '*')
              s
      | _ ->
            string loc ~comm_level bp (store len '(') s) s
  | Some '*' ->
      Stream.junk s;
      (fun s -> match Stream.peek s with
         | Some ')' ->
            Stream.junk s;
            let () = match comm_level with
            | Some 0 ->
              warn_comment_terminator_in_string ~loc ()
            | _ -> ()
            in
            let comm_level = Option.map pred comm_level in
            string loc ~comm_level bp (store (store len '*') ')') s
         | _ ->
            string loc ~comm_level bp (store len '*') s) s
  | Some ('\n' as c) ->
    Stream.junk s;
    let ep = Stream.count s in
     (* If we are parsing a comment, the string if not part of a token so we
     update the first line of the location. Otherwise, we update the last
     line. *)
     let loc =
       if Option.has_some comm_level then bump_loc_line loc ep
       else bump_loc_line_last loc ep
     in
     string loc ~comm_level bp (store len c) s
  | Some c ->
      Stream.junk s;
      string loc ~comm_level bp (store len c) s
  | _ ->
      let _ = Stream.empty s in
      let ep = Stream.count s in
     let loc = set_loc_pos loc bp ep in
     err loc Unterminated_string

(* Utilities for comments in beautify *)
let comment_begin = ref None
let comm_loc bp = match !comment_begin with
| None -> comment_begin := Some bp
| _ -> ()

let comments = ref []
let current_comment = Buffer.create 8192
let between_commands = ref true

(* The state of the lexer visible from outside *)
type lexer_state = int option * string * bool * ((int * int) * string) list

let init_lexer_state () = (None,"",true,[])
let set_lexer_state (o,s,b,c) =
  comment_begin := o;
  Buffer.clear current_comment; Buffer.add_string current_comment s;
  between_commands := b;
  comments := c
let get_lexer_state () =
  (!comment_begin, Buffer.contents current_comment, !between_commands, !comments)
let drop_lexer_state () =
    set_lexer_state (init_lexer_state ())

let get_comment_state (_,_,_,c) = c

let real_push_char c = Buffer.add_char current_comment c

(* Add a char if it is between two commands, if it is a newline or
   if the last char is not a space itself. *)
let push_char c =
  if
    !between_commands || List.mem c ['\n';'\r'] ||
    (List.mem c [' ';'\t']&&
     (Int.equal (Buffer.length current_comment) 0 ||
      not (let s = Buffer.contents current_comment in
           List.mem s.[String.length s - 1] [' ';'\t';'\n';'\r'])))
  then
    real_push_char c

let push_string s = Buffer.add_string current_comment s

let null_comment s =
  let rec null i =
    i<0 || (List.mem s.[i] [' ';'\t';'\n';'\r'] && null (i-1)) in
  null (String.length s - 1)

let comment_stop ep =
  let current_s = Buffer.contents current_comment in
  (if !Flags.beautify && Buffer.length current_comment > 0 &&
    (!between_commands || not(null_comment current_s)) then
    let bp = match !comment_begin with
        Some bp -> bp
      | None ->
          Feedback.msg_notice
            (str "No begin location for comment '"
             ++ str current_s ++str"' ending at  "
             ++ int ep);
          ep-1 in
    comments := ((bp,ep),current_s) :: !comments);
  Buffer.clear current_comment;
  comment_begin := None;
  between_commands := false

let rec comment loc bp s =
  let bp2 = Stream.count s in
  match Stream.peek s with
    Some '(' ->
      Stream.junk s;
      let loc =
        try
          match Stream.peek s with
            Some '*' ->
              Stream.junk s;
              push_string "(*"; comment loc bp s
          | _ -> push_string "("; loc
        with Stream.Failure -> raise (Stream.Error "")
      in
      comment loc bp s
  | Some '*' ->
      Stream.junk s;
      begin try
        match Stream.peek s with
          Some ')' -> Stream.junk s; push_string "*)"; loc
        | _ -> real_push_char '*'; comment loc bp s
      with Stream.Failure -> raise (Stream.Error "")
      end
  | Some '"' ->
      Stream.junk s;
      let loc, len = string loc ~comm_level:(Some 0) bp2 0 s in
      push_string "\""; push_string (get_buff len); push_string "\"";
      comment loc bp s
  | _ ->
    match try Some (Stream.empty s) with Stream.Failure -> None with
    | Some _ ->
      let ep = Stream.count s in
      let loc = set_loc_pos loc bp ep in
      err loc Unterminated_comment
    | _ ->
          match Stream.peek s with
            Some ('\n' as z) ->
              Stream.junk s;
              let ep = Stream.count s in
              real_push_char z; comment (bump_loc_line loc ep) bp s
          | Some z ->
              Stream.junk s;
              real_push_char z; comment loc bp s
          | _ -> raise Stream.Failure

(* Parse a special token, using the [token_tree] *)

(* Peek as much utf-8 lexemes as possible *)
(* and retain the longest valid special token obtained *)
let rec progress_further loc last nj tt cs =
  try progress_from_byte loc last nj tt cs (List.nth (Stream.npeek (nj+1) cs) nj)
  with Failure _ -> last

and update_longest_valid_token loc last nj tt cs =
  match tt.node with
  | Some _ as last' ->
    stream_njunk nj cs;
    progress_further loc last' 0 tt cs
  | None ->
    progress_further loc last nj tt cs

(* nj is the number of char peeked since last valid token *)
(* n the number of char in utf8 block *)
and progress_utf8 loc last nj n c tt cs =
  try
    let tt = CharMap.find c tt.branch in
    if Int.equal n 1 then
      update_longest_valid_token loc last (nj+n) tt cs
    else
      match Util.List.skipn (nj+1) (Stream.npeek (nj+n) cs) with
      | l when Int.equal (List.length l) (n - 1) ->
         List.iter (check_utf8_trailing_byte loc cs) l;
         let tt = List.fold_left (fun tt c -> CharMap.find c tt.branch) tt l in
         update_longest_valid_token loc last (nj+n) tt cs
      | _ ->
          error_utf8 loc cs
  with Not_found ->
    last

and progress_from_byte loc last nj tt cs c =
  progress_utf8 loc last nj (utf8_char_size loc cs c) c tt cs

type marker = Delimited of int * char list * char list | ImmediateAsciiIdent

let peek_marker_len b e s =
  let rec peek n =
    match stream_nth n s with
    | c -> if c = b then peek (n+1) else n, List.make n b, List.make n e
    | exception Stream.Failure -> n, List.make n b, List.make n e
  in
  let len, start, stop = peek 0 in
  if len = 0 then raise Stream.Failure
  else Delimited (len, start, stop)

let peek_marker s =
  match stream_nth 0 s with
    | '(' -> peek_marker_len '(' ')' s
    | '[' -> peek_marker_len '[' ']' s
    | '{' -> peek_marker_len '{' '}' s
    | ('a'..'z' | 'A'..'Z' | '_') -> ImmediateAsciiIdent
    | _ -> raise Stream.Failure

let parse_quotation loc bp s =
  match peek_marker s with
  | ImmediateAsciiIdent ->
      let c = Stream.next s in
      let len =
        try ident_tail loc (store 0 c) s with
          Stream.Failure -> raise (Stream.Error "")
      in
      get_buff len, set_loc_pos loc bp (Stream.count s)
  | Delimited (lenmarker, bmarker, emarker) ->
      let b = Buffer.create 80 in
      let commit1 c = Buffer.add_char b c; Stream.junk s in
      let commit l = List.iter commit1 l in
      let rec quotation loc depth =
        match Stream.npeek lenmarker s with
        | l when l = bmarker ->
              commit l;
              quotation loc (depth + 1)
        | l when l = emarker ->
              commit l;
              if depth > 1 then quotation loc (depth - 1) else loc
        | '\n' :: cs ->
              commit1 '\n';
              let loc = bump_loc_line_last loc (Stream.count s) in
              quotation loc depth
        | c :: cs ->
              commit1 c;
              quotation loc depth
        | [] -> raise Stream.Failure
      in
      let loc = quotation loc 0 in
      Buffer.contents b, set_loc_pos loc bp (Stream.count s)


let find_keyword loc id bp s =
  let tt = ttree_find !token_tree id in
  match progress_further loc tt.node 0 tt s with
  | None -> raise Not_found
  | Some (c,NoQuotation) ->
      let ep = Stream.count s in
      KEYWORD c, set_loc_pos loc bp ep
  | Some (c,Quotation) ->
      let txt, loc = parse_quotation loc bp s in
      QUOTATION(c, txt), loc

let process_sequence loc bp c cs =
  let rec aux n cs =
    match Stream.peek cs with
    | Some c' when c == c' -> Stream.junk cs; aux (n+1) cs
    | _ -> BULLET (String.make n c), set_loc_pos loc bp (Stream.count cs)
  in
  aux 1 cs

(* Must be a special token *)
let process_chars ~diff_mode loc bp c cs =
  let t = progress_from_byte loc None (-1) !token_tree cs c in
  let ep = Stream.count cs in
  match t with
    | Some (t,NoQuotation) -> (KEYWORD t, set_loc_pos loc bp ep)
    | Some (c,Quotation) ->
        let txt, loc = parse_quotation loc bp cs in
        QUOTATION(c, txt), loc
    | None ->
        let ep' = bp + utf8_char_size loc cs c in
        if diff_mode then begin
          let len = ep' - bp in
          ignore (store 0 c);
          ignore (nstore (len - 1) 1 cs);
          IDENT (get_buff len), set_loc_pos loc bp ep
        end else begin
          njunk (ep' - ep) cs;
          let loc = set_loc_pos loc bp ep' in
          err loc Undefined_token
        end

(* Parse what follows a dot *)

let parse_after_dot ~diff_mode loc c bp s = match Stream.peek s with
  | Some ('a'..'z' | 'A'..'Z' | '_' as d) ->
      Stream.junk s;
      let len =
        try ident_tail loc (store 0 d) s with
          Stream.Failure -> raise (Stream.Error "")
      in
      let field = get_buff len in
      begin try find_keyword loc ("."^field) bp s
      with Not_found ->
        let ep = Stream.count s in
        FIELD field, set_loc_pos loc bp ep end
  | _ ->
      match lookup_utf8 loc s with
      | Utf8Token (st, n) when Unicode.is_valid_ident_initial st ->
          let len = ident_tail loc (nstore n 0 s) s in
          let field = get_buff len in
          begin try find_keyword loc ("."^field) bp s
          with Not_found ->
            let ep = Stream.count s in
            FIELD field, set_loc_pos loc bp ep end
      | AsciiChar | Utf8Token _ | EmptyStream ->
          process_chars ~diff_mode loc bp c s

(* Parse what follows a question mark *)

let parse_after_qmark ~diff_mode loc bp s =
  match Stream.peek s with
    | Some ('a'..'z' | 'A'..'Z' | '_') -> LEFTQMARK
    | None -> KEYWORD "?"
    | _ ->
        match lookup_utf8 loc s with
          | Utf8Token (st, _) when Unicode.is_valid_ident_initial st -> LEFTQMARK
          | AsciiChar | Utf8Token _ | EmptyStream ->
            fst (process_chars ~diff_mode loc bp '?' s)

let blank_or_eof cs =
  match Stream.peek cs with
    | None -> true
    | Some (' ' | '\t' | '\n' |'\r') -> true
    | _ -> false

(* Parse a token in a char stream *)

let rec next_token ~diff_mode loc s =
  let bp = Stream.count s in
  match Stream.peek s with
  | Some ('\n' as c) ->
      Stream.junk s;
      let ep = Stream.count s in
      comm_loc bp; push_char c; next_token ~diff_mode (bump_loc_line loc ep) s
  | Some (' ' | '\t' | '\r' as c) ->
      Stream.junk s;
      comm_loc bp; push_char c; next_token ~diff_mode loc s
  | Some ('.' as c) ->
      Stream.junk s;
      let t, newloc =
        try parse_after_dot ~diff_mode loc c bp s with
          Stream.Failure -> raise (Stream.Error "")
      in
      comment_stop bp;
      (* We enforce that "." should either be part of a larger keyword,
         for instance ".(", or followed by a blank or eof. *)
      let () = match t with
        | KEYWORD ("." | "...") ->
          if not (blank_or_eof s) then begin
            let ep = Stream.count s in
            err (set_loc_pos loc bp (ep+1)) Undefined_token
          end;
          between_commands := true;
        | _ -> ()
      in
      t, newloc
  | Some ('-' | '+' | '*' as c) ->
      Stream.junk s;
      let t,new_between_commands =
        if !between_commands then process_sequence loc bp c s, true
        else process_chars ~diff_mode loc bp c s,false
      in
      comment_stop bp; between_commands := new_between_commands; t
  | Some '?' ->
      Stream.junk s;
      let ep = Stream.count s in
      let t = parse_after_qmark ~diff_mode loc bp s in
      comment_stop bp; (t, set_loc_pos loc bp ep)
  | Some ('a'..'z' | 'A'..'Z' | '_' as c) ->
      Stream.junk s;
      let len =
        try ident_tail loc (store 0 c) s with
          Stream.Failure -> raise (Stream.Error "")
      in
      let id = get_buff len in
      comment_stop bp;
      begin try find_keyword loc id bp s
      with Not_found ->
        let ep = Stream.count s in
        IDENT id, set_loc_pos loc bp ep end
  | Some ('0'..'9') ->
      let n = NumTok.parse s in
      let ep = Stream.count s in
      comment_stop bp;
      (NUMERAL n, set_loc_pos loc bp ep)
  | Some '\"' ->
      Stream.junk s;
      let (loc, len) =
        try string loc ~comm_level:None bp 0 s with
          Stream.Failure -> raise (Stream.Error "")
      in
      let ep = Stream.count s in
      comment_stop bp;
      (STRING (get_buff len), set_loc_pos loc bp ep)
  | Some ('(' as c) ->
      Stream.junk s;
      begin try
        match Stream.peek s with
        | Some '*' when diff_mode ->
            Stream.junk s;
            let ep = Stream.count s in
            (IDENT "(*", set_loc_pos loc bp ep)
        | Some '*' ->
            Stream.junk s;
            comm_loc bp;
            push_string "(*";
            let loc = comment loc bp s in next_token ~diff_mode loc s
        | _ -> let t = process_chars ~diff_mode loc bp c s in comment_stop bp; t
      with Stream.Failure -> raise (Stream.Error "")
      end
  | Some ('{' | '}' as c) ->
      Stream.junk s;
      let ep = Stream.count s in
      let t,new_between_commands =
        if !between_commands then (KEYWORD (String.make 1 c), set_loc_pos loc bp ep), true
        else process_chars ~diff_mode loc bp c s, false
      in
      comment_stop bp; between_commands := new_between_commands; t
  | _ ->
      match lookup_utf8 loc s with
        | Utf8Token (st, n) when Unicode.is_valid_ident_initial st ->
            let len = ident_tail loc (nstore n 0 s) s in
            let id = get_buff len in
            comment_stop bp;
            begin try find_keyword loc id bp s
            with Not_found ->
              let ep = Stream.count s in
              IDENT id, set_loc_pos loc bp ep end
        | AsciiChar | Utf8Token _ ->
            let t = process_chars ~diff_mode loc bp (Stream.next s) s in
            comment_stop bp; t
        | EmptyStream ->
            comment_stop bp; (EOI, set_loc_pos loc bp (bp+1))

(* (* Debug: uncomment this for tracing tokens seen by coq...*)
let next_token ~diff_mode loc s =
  let (t,loc as r) = next_token ~diff_mode loc s in
  Printf.eprintf "(line %i, %i-%i)[%s]\n%!" (Ploc.line_nb loc) (Ploc.first_pos loc) (Ploc.last_pos loc) (Tok.to_string t);
  r *)

(* Location table system for creating tables associating a token count
   to its location in a char stream (the source) *)

let locerr () = invalid_arg "Lexer: location function"

let loct_create () = Hashtbl.create 207

let loct_func loct i =
  try Hashtbl.find loct i with Not_found -> locerr ()

let loct_add loct i loc = Hashtbl.add loct i loc

(** {6 The lexer of Coq} *)

(** Note: removing a token.
   We do nothing because [remove_token] is called only when removing a grammar
   rule with [Grammar.delete_rule]. The latter command is called only when
   unfreezing the state of the grammar entries (see GRAMMAR summary, file
   env/metasyntax.ml). Therefore, instead of removing tokens one by one,
   we unfreeze the state of the lexer. This restores the behaviour of the
   lexer. B.B. *)

(** Names of tokens, for this lexer, used in Grammar error messages *)

let token_text : type c. c Tok.p -> string = function
  | PKEYWORD t -> "'" ^ t ^ "'"
  | PIDENT None -> "identifier"
  | PIDENT (Some t) -> "'" ^ t ^ "'"
  | PNUMERAL None -> "numeral"
  | PNUMERAL (Some n) -> "'" ^ NumTok.to_string n ^ "'"
  | PSTRING None -> "string"
  | PSTRING (Some s) -> "STRING \"" ^ s ^ "\""
  | PLEFTQMARK -> "LEFTQMARK"
  | PEOI -> "end of input"
  | PPATTERNIDENT None -> "PATTERNIDENT"
  | PPATTERNIDENT (Some s) -> "PATTERNIDENT \"" ^ s ^ "\""
  | PFIELD None -> "FIELD"
  | PFIELD (Some s) -> "FIELD \"" ^ s ^ "\""
  | PBULLET None -> "BULLET"
  | PBULLET (Some s) -> "BULLET \"" ^ s ^ "\""
  | PQUOTATION lbl -> "QUOTATION \"" ^ lbl ^ "\""

let func next_token ?loc cs =
  let loct = loct_create () in
  let cur_loc = ref (Option.default Loc.(initial ToplevelInput) loc) in
  let ts =
    Stream.from
      (fun i ->
         let (tok, loc) = next_token !cur_loc cs in
	 cur_loc := after loc;
         loct_add loct i loc; Some tok)
  in
  (ts, loct_func loct)

module MakeLexer (Diff : sig val mode : bool end) = struct
  type te = Tok.t
  type 'c pattern = 'c Tok.p
  let tok_pattern_eq = Tok.equal_p
  let tok_pattern_strings = Tok.pattern_strings
  let tok_func = func (next_token ~diff_mode:Diff.mode)
  let tok_using : type c. c pattern -> unit = function
    | PKEYWORD s -> add_keyword ~quotation:NoQuotation s
    | PQUOTATION s -> add_keyword ~quotation:Quotation s
    | _ -> ()
  let tok_removing = (fun _ -> ())
  let tok_match = Tok.match_pattern
  let tok_text = token_text
end

module Lexer = MakeLexer (struct let mode = false end)

module LexerDiff = MakeLexer (struct let mode = true end)

(** Terminal symbols interpretation *)

let is_ident_not_keyword s =
  is_ident s && not (is_keyword s)

let strip s =
  let len =
    let rec loop i len =
      if Int.equal i (String.length s) then len
      else if s.[i] == ' ' then loop (i + 1) len
      else loop (i + 1) (len + 1)
    in
    loop 0 0
  in
  if len == String.length s then s
  else
    let s' = Bytes.create len in
    let rec loop i i' =
      if i == String.length s then s'
      else if s.[i] == ' ' then loop (i + 1) i'
      else begin Bytes.set s' i' s.[i]; loop (i + 1) (i' + 1) end
    in
    Bytes.to_string (loop 0 0)

let terminal s =
  let s = strip s in
  let () = match s with "" -> failwith "empty token." | _ -> () in
  if is_ident_not_keyword s then PIDENT (Some s)
  else PKEYWORD s

(* Precondition: the input is a numeral (c.f. [NumTok.t]) *)
let terminal_numeral s = match NumTok.of_string s with
  | Some n -> PNUMERAL (Some n)
  | None -> failwith "numeral token expected."
