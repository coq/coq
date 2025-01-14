(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Tok

module Stream = Gramlib.Stream

(* Dictionaries: trees annotated with string options, each node being a map
   from chars to dictionaries (the subtrees). A trie, in other words. *)

module CharOrd = struct type t = char let compare : char -> char -> int = compare end
module CharMap = Map.Make (CharOrd)

type starts_quotation = NoQuotation | Quotation

type ttree = {
  node : (string * starts_quotation) option;
  branch : ttree CharMap.t;
}

let empty_keyword_state = { node = None; branch = CharMap.empty }

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
  Loc.sub loc (bp - loc.Loc.bp) (ep - bp)

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
  | EmptyStream

let error_utf8 loc cs =
  let bp = Stream.count cs in
  Stream.junk () cs; (* consume the char to avoid read it and fail again *)
  let loc = set_loc_pos loc bp (bp+1) in
  err loc Illegal_character

let check_utf8_trailing_byte loc cs c =
  if not (Int.equal (Char.code c land 0xC0) 0x80) then error_utf8 loc cs

(* Recognize utf8 blocks (of length less than 4 bytes) *)
(* but don't certify full utf8 compliance (e.g. no emptyness check) *)
let lookup_utf8_char loc nj cs =
  match try Some (List.nth (Stream.npeek () (nj+1) cs) nj) with Failure _ -> None with
  | None -> []
  | Some c1 ->
    match c1 with
    | '\x00'..'\x7F' -> [c1]
    | c1 ->
      let c1 = Char.code c1 in
      if Int.equal (c1 land 0x40) 0 || Int.equal (c1 land 0x38) 0x38 then error_utf8 loc cs else
      if Int.equal (c1 land 0x20) 0 then
        match List.skipn nj (Stream.npeek () (nj+2) cs) with
        | [_;c2] as l -> check_utf8_trailing_byte loc cs c2; l
        | _ -> error_utf8 loc cs
      else if Int.equal (c1 land 0x10) 0 then
        match List.skipn nj (Stream.npeek () (nj+3) cs) with
        | [_;c2;c3] as l ->
          check_utf8_trailing_byte loc cs c2;
          check_utf8_trailing_byte loc cs c3;
          l
        | _ -> error_utf8 loc cs
      else match List.skipn nj (Stream.npeek () (nj+4) cs) with
      | [_;c2;c3;c4] as l ->
          check_utf8_trailing_byte loc cs c2;
          check_utf8_trailing_byte loc cs c3;
          check_utf8_trailing_byte loc cs c4;
          l
      | _ -> error_utf8 loc cs

let status_of_utf8 = function
  | [] -> EmptyStream
  | l ->
    let n, unicode = match l with
    | [c1] -> 1, Char.code c1
    | [c1;c2] -> 2, (Char.code c1 land 0x1F) lsl 6 + (Char.code c2 land 0x3F)
    | [c1;c2;c3] ->
       3, (Char.code c1 land 0x0F) lsl 12 + (Char.code c2 land 0x3F) lsl 6 +
            (Char.code c3 land 0x3F)
    | [c1;c2;c3;c4] ->
       4, (Char.code c1 land 0x07) lsl 18 + (Char.code c2 land 0x3F) lsl 12 +
            (Char.code c3 land 0x3F) lsl 6 + (Char.code c4 land 0x3F)
    | _ -> assert false
    in
    Utf8Token (Unicode.classify unicode, n)

let lookup_utf8 loc cs =
  status_of_utf8 (lookup_utf8_char loc 0 cs)

let is_letter l =
  match status_of_utf8 l with
  | EmptyStream -> false
  | Utf8Token (st,_) -> Unicode.is_letter st

let unlocated f x =
  let dummy_loc = Loc.(initial ToplevelInput) in
  f dummy_loc x
  (** FIXME: should we still unloc the exception? *)
(*   try f x with Loc.Exc_located (_, exc) -> raise exc *)

let check_keyword str =
  let rec loop_symb s = match Stream.peek () s with
    | Some (' ' | '\n' | '\r' | '\t') ->
        Stream.junk () s;
        bad_token str
    | _ ->
        match unlocated lookup_utf8 s with
        | Utf8Token (_,n) -> Stream.njunk () n s; loop_symb s
        | EmptyStream -> ()
  in
  loop_symb (Stream.of_string str)

let check_ident str =
  let rec loop_id intail s =
    match unlocated lookup_utf8 s with
    | Utf8Token (st, n) when not intail && Unicode.is_valid_ident_initial st ->
      Stream.njunk () n s; loop_id true s
    | Utf8Token (st, n) when intail && Unicode.is_valid_ident_trailing st ->
      Stream.njunk () n s;
      loop_id true s
    | EmptyStream -> ()
    | Utf8Token _ -> bad_token str
  in
  loop_id false (Stream.of_string str)

let is_ident str =
  try let _ = check_ident str in true with Error.E _ -> false

let is_keyword ttree s =
  try match (ttree_find ttree s).node with None -> false | Some _ -> true
  with Not_found -> false

let add_keyword ?(quotation=NoQuotation) ttree str =
  if not (is_keyword ttree str) then
    begin
      check_keyword str;
      ttree_add ttree (str,quotation)
    end
  else ttree

let add_keyword_tok : type c. _ -> c Tok.p -> _ = fun ttree -> function
  | PKEYWORD s -> add_keyword ~quotation:NoQuotation ttree s
  | PQUOTATION s -> add_keyword ~quotation:Quotation ttree s
  | _ -> ttree

let keywords = ttree_elements

(* Freeze and unfreeze the state of the lexer *)
type keyword_state = ttree

(* The string buffering machinery *)

let buff = ref (Bytes.create 80)

let store len x =
  let open Bytes in
  if len >= length !buff then
    buff := cat !buff (create (length !buff));
  set !buff len x;
  succ len

let rec nstore n len cs =
  if n>0 then nstore (n-1) (store len (Stream.next () cs)) cs else len

let get_buff len = Bytes.sub_string !buff 0 len

(* The classical lexer: idents, numbers, quoted strings, comments *)

let warn_unrecognized_unicode =
  CWarnings.create ~name:"unrecognized-unicode" ~category:CWarnings.CoreCategories.parsing
         (fun (u,id) ->
          strbrk (Printf.sprintf "Not considering unicode character \"%s\" of unknown \
                                  lexical status as part of identifier \"%s\"." u id))

let rec ident_tail loc len s =
  match lookup_utf8 loc s with
  | Utf8Token (st, n) when Unicode.is_valid_ident_trailing st ->
      ident_tail loc (nstore n len s) s
  | Utf8Token (st, n) when Unicode.is_unknown st ->
      let id = get_buff len in
      let u = String.concat "" (List.map (String.make 1) (Stream.npeek () n s)) in
      warn_unrecognized_unicode ~loc (u,id); len
  | _ -> len

let warn_comment_terminator_in_string =
  CWarnings.create ~name:"comment-terminator-in-string" ~category:CWarnings.CoreCategories.parsing
         (fun () ->
          (strbrk
             "Not interpreting \"*)\" as the end of current \
              non-terminated comment because it occurs in a \
              non-terminated string of the comment."))

(* If the string being lexed is in a comment, [comm_level] is Some i with i the
   current level of comments nesting. Otherwise, [comm_level] is None. *)
let rec string loc ~comm_level bp len s = match Stream.peek () s with
  | Some '"' ->
      Stream.junk () s;
      let esc =
        match Stream.peek () s with
          Some '"' -> Stream.junk () s; true
        | _ -> false
      in
      if esc then string loc ~comm_level bp (store len '"') s else (loc, len)
  | Some '(' ->
      Stream.junk () s;
      (fun s -> match Stream.peek () s with
      | Some '*' ->
        Stream.junk () s;
        let comm_level = Option.map succ comm_level in
            string loc ~comm_level
              bp (store (store len '(') '*')
              s
      | _ ->
            string loc ~comm_level bp (store len '(') s) s
  | Some '*' ->
      Stream.junk () s;
      (fun s -> match Stream.peek () s with
         | Some ')' ->
            Stream.junk () s;
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
    Stream.junk () s;
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
      Stream.junk () s;
      string loc ~comm_level bp (store len c) s
  | _ ->
    let () = if not (Stream.is_empty () s) then raise Stream.Failure in
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

let real_push_char c = Buffer.add_char current_comment c

let push_string s = Buffer.add_string current_comment s

let dbg = CDebug.create ~name:"comment-lexing" ()

let comment_stop ep =
  let current_s = Buffer.contents current_comment in
  (if !Flags.record_comments && Buffer.length current_comment > 0 then
    let bp = match !comment_begin with
        Some bp -> bp
      | None ->
          Feedback.msg_debug
            (str "No begin location for comment '"
             ++ str current_s ++str"' ending at  "
             ++ int ep);
          ep-1 in
    dbg Pp.(fun () ->
        str "comment at chars " ++ int bp ++ str "-" ++ int ep ++ str ":" ++ fnl() ++
        str current_s);
    comments := ((bp,ep),current_s) :: !comments);
  Buffer.clear current_comment;
  comment_begin := None

let rec comment loc bp s =
  let bp2 = Stream.count s in
  match Stream.peek () s with
    Some '(' ->
      Stream.junk () s;
      let loc =
        try
          match Stream.peek () s with
            Some '*' ->
              Stream.junk () s;
              push_string "(*"; comment loc bp s
          | _ -> push_string "("; loc
        with Stream.Failure -> raise (Gramlib.Grammar.Error "")
      in
      comment loc bp s
  | Some '*' ->
      Stream.junk () s;
      begin try
        match Stream.peek () s with
          Some ')' -> Stream.junk () s; push_string "*)"; loc
        | _ -> real_push_char '*'; comment loc bp s
      with Stream.Failure -> raise (Gramlib.Grammar.Error "")
      end
  | Some '"' ->
      Stream.junk () s;
      let loc, len = string loc ~comm_level:(Some 0) bp2 0 s in
      push_string "\""; push_string (get_buff len); push_string "\"";
      comment loc bp s
  | _ ->
    match Stream.is_empty () s with
    | true ->
      let ep = Stream.count s in
      let loc = set_loc_pos loc bp ep in
      err loc Unterminated_comment
    | false ->
          match Stream.peek () s with
            Some ('\n' as z) ->
              Stream.junk () s;
              let ep = Stream.count s in
              real_push_char z; comment (bump_loc_line loc ep) bp s
          | Some z ->
              Stream.junk () s;
              real_push_char z; comment loc bp s
          | _ -> raise Stream.Failure

(* Parse a special token, using the [token_tree] *)

(* Below, [last] is the last valid token found in the table *)
(* [nj] is the number of bytes read since then and *)
(* these bytes form a complete utf-8 sequence *)
(* [tt] is the tree after having taken into account these [nj] bytes *)

let update_longest_valid_token last nj tt cs =
  match tt.node with
  | Some _ as last' ->
    (* [last] extended with the [nj] bytes constitutes a valid token *)
    (* we update cs, last and nj *)
    Stream.njunk () nj cs; 0, last'
  | None ->
    (* [last] extended with the [nj] bytes does not form a full valid token *)
    nj, last

(* try to progress by peeking the next utf-8 lexeme *)
(* and retain the longest valid special token obtained *)
let rec progress_further loc last nj last_is_letter tt cs =
  match lookup_utf8_char loc nj cs with
  | [] -> snd (update_longest_valid_token last nj tt cs)
  | l -> progress_utf8 loc last nj last_is_letter tt cs l

(* under the same assumptions as [update_longest_valid_token], *)
(* read the [n] bytes of the current utf-8 lexeme whose first byte is [c] *)
and progress_utf8 loc last nj last_is_letter tt cs l =
  let is_letter' = is_letter l in
  (* compute longest match before considering utf8 block [l] *)
  (* not allowing update if in the middle of an ident part *)
  let nj, last = if last_is_letter && is_letter' then nj, last else update_longest_valid_token last nj tt cs in
  try
    (* descend in tree according to current utf8 block [l] *)
    let tt = List.fold_left (fun tt c -> CharMap.find c tt.branch) tt l in
    progress_further loc last (nj + List.length l) is_letter' tt cs
  with Not_found ->
    last

let blank_or_eof cs =
  match Stream.peek () cs with
    | None -> true
    | Some (' ' | '\t' | '\n' |'\r') -> true
    | _ -> false

type marker = Delimited of int * char list * char list | ImmediateAsciiIdent

let peek_marker_len b e s =
  let rec peek n =
    match Stream.nth () n s with
    | c -> if c = b then peek (n+1) else n, List.make n b, List.make n e
    | exception Stream.Failure -> n, List.make n b, List.make n e
  in
  let len, start, stop = peek 0 in
  if len = 0 then raise Stream.Failure
  else Delimited (len, start, stop)

let peek_marker s =
  match Stream.nth () 0 s with
    | '(' -> peek_marker_len '(' ')' s
    | '[' -> peek_marker_len '[' ']' s
    | '{' -> peek_marker_len '{' '}' s
    | ('a'..'z' | 'A'..'Z' | '_') -> ImmediateAsciiIdent
    | _ -> raise Stream.Failure

let parse_quotation loc bp s =
  match peek_marker s with
  | ImmediateAsciiIdent ->
      let c = Stream.next () s in
      let len =
        try ident_tail loc (store 0 c) s with
          Stream.Failure -> raise (Gramlib.Grammar.Error "")
      in
      get_buff len, set_loc_pos loc bp (Stream.count s)
  | Delimited (lenmarker, bmarker, emarker) ->
      let dot_gobbling =
        (* only quotations starting with two curly braces can gobble sentences *)
        match bmarker with
        | '{' :: '{' :: _ -> true
        | _ -> false in
      let b = Buffer.create 80 in
      let commit1 c = Buffer.add_char b c; Stream.junk () s in
      let commit l = List.iter commit1 l in
      let rec quotation loc depth =
        match Stream.npeek () lenmarker s with
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
        | '.' :: _ ->
              commit1 '.';
              if not dot_gobbling && blank_or_eof s then raise Stream.Failure;
              quotation loc depth
        | c :: cs ->
              commit1 c;
              quotation loc depth
        | [] -> raise Stream.Failure
      in
      let loc = quotation loc 0 in
      Buffer.contents b, set_loc_pos loc bp (Stream.count s)

let peek_string v s =
  let l = String.length v in
  let rec aux i =
    if Int.equal i l then true
    else
      let l' = Stream.npeek () (i + 1) s in
      match List.nth_opt l' i with
      | Some c -> Char.equal c v.[i] && aux (i + 1)
      | None -> false (* EOF *) in
  aux 0

let find_keyword ttree loc id bp s =
  if peek_string ":{{" s then
    begin
      (* "xxx:{{" always starts a sentence-gobbling quotation, whether registered or not *)
      Stream.junk () s;
      let txt, loc = parse_quotation loc bp s in
      QUOTATION (id ^ ":", txt), loc
    end
  else
  let tt = ttree_find ttree id in
  match progress_further loc tt.node 0 true tt s with
  | None -> raise Not_found
  | Some (c,NoQuotation) ->
      let ep = Stream.count s in
      KEYWORD c, set_loc_pos loc bp ep
  | Some (c,Quotation) ->
      let txt, loc = parse_quotation loc bp s in
      QUOTATION(c, txt), loc

let process_sequence loc bp c cs =
  let rec aux n cs =
    match Stream.peek () cs with
    | Some c' when c == c' -> Stream.junk () cs; aux (n+1) cs
    | _ -> BULLET (String.make n c), set_loc_pos loc bp (Stream.count cs)
  in
  aux 1 cs

(* Must be a special token *)
let process_chars ~diff_mode ttree loc bp l cs =
  let t = progress_utf8 loc None (- (List.length l)) false ttree cs l in
  let ep = Stream.count cs in
  match t with
    | Some (t,NoQuotation) -> (KEYWORD t, set_loc_pos loc bp ep)
    | Some (c,Quotation) ->
        let txt, loc = parse_quotation loc bp cs in
        QUOTATION(c, txt), loc
    | None ->
        if diff_mode then begin
          let s = String.concat "" (List.map (String.make 1) l) in
          IDENT s, set_loc_pos loc bp ep
        end else begin
          let loc = set_loc_pos loc bp ep in
          err loc Undefined_token
        end

(* Parse what follows a dot *)

let parse_after_dot ~diff_mode ttree loc c bp s =
  match lookup_utf8 loc s with
  | Utf8Token (st, n) when Unicode.is_valid_ident_initial st ->
      let len = ident_tail loc (nstore n 0 s) s in
      let field = get_buff len in
      begin try find_keyword ttree loc ("."^field) bp s
            with Not_found ->
              let ep = Stream.count s in
              FIELD field, set_loc_pos loc bp ep end
  | Utf8Token _ | EmptyStream ->
      process_chars ~diff_mode ttree loc bp [c] s

(* Parse what follows a question mark *)

let parse_after_qmark ~diff_mode ttree loc bp s =
  match lookup_utf8 loc s with
  | Utf8Token (st, _) when Unicode.is_valid_ident_initial st -> LEFTQMARK
  | EmptyStream -> KEYWORD "?"
  | Utf8Token _ -> fst (process_chars ~diff_mode ttree loc bp ['?'] s)

(* Parse a token in a char stream *)

(* between_commands is used to parse bullets and { and } differently depending on the context. *)
let between_commands = ref true

let rec next_token ~diff_mode ttree loc s =
  let bp = Stream.count s in
  match Stream.peek () s with
  | Some '\n' ->
      Stream.junk () s;
      let ep = Stream.count s in
      next_token ~diff_mode ttree (bump_loc_line loc ep) s
  | Some (' ' | '\t' | '\r') ->
      Stream.junk () s;
      next_token ~diff_mode ttree loc s
  | Some ('.' as c) ->
      Stream.junk () s;
      let t, newloc =
        try parse_after_dot ~diff_mode ttree loc c bp s with
          Stream.Failure -> raise (Gramlib.Grammar.Error "")
      in
      between_commands := false;
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
      Stream.junk () s;
      let t,new_between_commands =
        if !between_commands then process_sequence loc bp c s, true
        else process_chars ~diff_mode ttree loc bp [c] s,false
      in
      between_commands := new_between_commands; t
  | Some '?' ->
      Stream.junk () s;
      let ep = Stream.count s in
      let t = parse_after_qmark ~diff_mode ttree loc bp s in
      between_commands := false;
      (t, set_loc_pos loc bp ep)
  | Some ('a'..'z' | 'A'..'Z' | '_' as c) ->
      Stream.junk () s;
      let len =
        try ident_tail loc (store 0 c) s with
          Stream.Failure -> raise (Gramlib.Grammar.Error "")
      in
      let id = get_buff len in
      between_commands := false;
      begin try find_keyword ttree loc id bp s
      with Not_found ->
        let ep = Stream.count s in
        IDENT id, set_loc_pos loc bp ep end
  | Some ('0'..'9') ->
      let n = NumTok.Unsigned.parse s in
      between_commands := false;
      begin try find_keyword ttree loc (NumTok.Unsigned.sprint n) bp s
      with Not_found ->
        let ep = Stream.count s in
        NUMBER n, set_loc_pos loc bp ep end
  | Some '\"' ->
      Stream.junk () s;
      let (loc, len) =
        try string loc ~comm_level:None bp 0 s with
          Stream.Failure -> raise (Gramlib.Grammar.Error "")
      in
      let ep = Stream.count s in
      between_commands := false;
      let str = get_buff len in
      begin try find_keyword ttree loc (CString.quote_coq_string str) bp s
      with Not_found ->
      (STRING str, set_loc_pos loc bp ep) end
  | Some ('(' as c) ->
      Stream.junk () s;
      begin try
        match Stream.peek () s with
        | Some '*' when diff_mode ->
            Stream.junk () s;
            let ep = Stream.count s in
            (IDENT "(*", set_loc_pos loc bp ep)
        | Some '*' ->
            Stream.junk () s;
            comm_loc bp;
            push_string "(*";
            let loc = comment loc bp s in
            comment_stop (Stream.count s);
            next_token ~diff_mode ttree loc s
        | _ ->
          let t = process_chars ~diff_mode ttree loc bp [c] s in
          between_commands := false;
          t
      with Stream.Failure -> raise (Gramlib.Grammar.Error "")
      end
  | Some ('{' | '}' as c) ->
      Stream.junk () s;
      let ep = Stream.count s in
      let t,new_between_commands =
        if !between_commands then (KEYWORD (String.make 1 c), set_loc_pos loc bp ep), true
        else process_chars ~diff_mode ttree loc bp [c] s, false
      in
      between_commands := new_between_commands; t
  | _ ->
      let l = lookup_utf8_char loc 0 s in
      match status_of_utf8 l with
        | Utf8Token (st, n) when Unicode.is_valid_ident_initial st ->
            let len = ident_tail loc (nstore n 0 s) s in
            let id = get_buff len in
            between_commands := false;
            begin try find_keyword ttree loc id bp s
            with Not_found ->
              let ep = Stream.count s in
              IDENT id, set_loc_pos loc bp ep end
        | Utf8Token (_, n) ->
            Stream.njunk () n s;
            let t = process_chars ~diff_mode ttree loc bp l s in
            between_commands := false;
            t
        | EmptyStream ->
            between_commands := false;
            (EOI, set_loc_pos loc bp (bp+1))

(* Reify exceptions for next_token, it would be really nice if we
   could actually delimit what this function raises, for now Error.E *)
let next_token ~diff_mode ttree loc s : (Tok.t * Loc.t, Exninfo.iexn) Result.t =
  let f (diff_mode, ttree, loc, s) = next_token ~diff_mode ttree loc s in
  CErrors.to_result ~f (diff_mode, ttree, loc, s)

(** {6 The lexer of Rocq} *)

module MakeLexer (Diff : sig val mode : bool end)
  : Gramlib.Plexing.S
    with type keyword_state = keyword_state
     and type te = Tok.t
     and type 'c pattern = 'c Tok.p
= struct
  type nonrec keyword_state = keyword_state
  type te = Tok.t
  type 'c pattern = 'c Tok.p
  let tok_pattern_eq = Tok.equal_p
  let tok_pattern_strings = Tok.pattern_strings
  let tok_func ?(loc=Loc.(initial ToplevelInput)) cs =
    let cur_loc = ref loc in
    Gramlib.LStream.from ~loc
      (fun ttree ->
         match next_token ~diff_mode:Diff.mode ttree !cur_loc cs with
         | Ok (tok, loc) ->
           cur_loc := after loc;
           Some (tok,loc)
         | Error (exn, info) ->
           (* If the error contains the location of the failing token,
              we still need to update [cur_loc] as to resume parsing
              correctly after the error. See
              https://github.com/ejgallego/coq-lsp/issues/633 for an
              example. *)
           let loc = Loc.get_loc info in
           Option.iter (fun loc -> cur_loc := after loc) loc;
           Exninfo.iraise (exn, info))
  let tok_match = Tok.match_pattern
  let tok_text = Tok.token_text

  (* The state of the lexer visible from outside *)
  module State = struct

    type t = int option * string * bool * ((int * int) * string) list

    let init () = (None,"",true,[])
    let set (o,s,b,c) =
      comment_begin := o;
      Buffer.clear current_comment; Buffer.add_string current_comment s;
      between_commands := b;
      comments := c
    let get () =
      (!comment_begin, Buffer.contents current_comment, !between_commands, !comments)
    let drop () = set (init ())
    let get_comments (_,_,_,c) = c

  end
end

module Lexer = MakeLexer (struct let mode = false end)

module LexerDiff = MakeLexer (struct let mode = true end)

(** Terminal symbols interpretation *)

let is_ident_not_keyword ttree s =
  is_ident s && not (is_keyword ttree s)

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

let terminal ttree s =
  let s = strip s in
  let () = match s with "" -> failwith "empty token." | _ -> () in
  if is_ident_not_keyword ttree s then PIDENT (Some s)
  else PKEYWORD s

(* Precondition: the input is a number (c.f. [NumTok.t]) *)
let terminal_number s = match NumTok.Unsigned.parse_string s with
  | Some n -> PNUMBER (Some n)
  | None -> failwith "number token expected."
