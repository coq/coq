(* camlp5r *)
(* plexing.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Versdep;

type pattern = (string * string);

exception Error of string;

type location = Ploc.t;
type location_function = int -> location;
type lexer_func 'te = Stream.t char -> (Stream.t 'te * location_function);

type lexer 'te =
  { tok_func : lexer_func 'te;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    tok_match : mutable pattern -> 'te -> string;
    tok_text : pattern -> string;
    tok_comm : mutable option (list location) }
;

value make_loc = Ploc.make_unlined;
value dummy_loc = Ploc.dummy;

value lexer_text (con, prm) =
  if con = "" then "'" ^ prm ^ "'"
  else if prm = "" then con
  else con ^ " '" ^ prm ^ "'"
;

value locerr () = failwith "Lexer: location function";
value loct_create () = (ref (array_create 1024 None), ref False);
value loct_func (loct, ov) i =
  match
    if i < 0 || i >= Array.length loct.val then
      if ov.val then Some dummy_loc else None
    else Array.unsafe_get loct.val i
  with
  [ Some loc -> loc
  | None -> locerr () ]
;
value loct_add (loct, ov) i loc =
  if i >= Array.length loct.val then
    let new_tmax = Array.length loct.val * 2 in
    if new_tmax < Sys.max_array_length then do {
      let new_loct = array_create new_tmax None in
      Array.blit loct.val 0 new_loct 0 (Array.length loct.val);
      loct.val := new_loct;
      loct.val.(i) := Some loc
    }
    else ov.val := True
  else loct.val.(i) := Some loc
;

value make_stream_and_location next_token_loc =
  let loct = loct_create () in
  let ts =
    Stream.from
      (fun i -> do {
         let (tok, loc) = next_token_loc () in
         loct_add loct i loc;
         Some tok
       })
  in
  (ts, loct_func loct)
;

value lexer_func_of_parser next_token_loc cs =
  let line_nb = ref 1 in
  let bolpos = ref 0 in
  make_stream_and_location (fun () -> next_token_loc (cs, line_nb, bolpos))
;

value lexer_func_of_ocamllex lexfun cs =
  let lb =
    Lexing.from_function
      (fun s n ->
         try do { string_set s 0 (Stream.next cs); 1 } with
         [ Stream.Failure -> 0 ])
  in
  let next_token_loc _ =
    let tok = lexfun lb in
    let loc = make_loc (Lexing.lexeme_start lb, Lexing.lexeme_end lb) in
    (tok, loc)
  in
  make_stream_and_location next_token_loc
;

(* Char and string tokens to real chars and string *)

value buff = ref (string_create 80);
value store len x = do {
  if len >= string_length buff.val then
    buff.val := string_cat buff.val (string_create (string_length buff.val))
  else ();
  string_set buff.val len x;
  succ len
};
value get_buff len = string_sub buff.val 0 len;

value valch x = Char.code x - Char.code '0';
value valch_a x = Char.code x - Char.code 'a' + 10;
value valch_A x = Char.code x - Char.code 'A' + 10;

value rec backslash s i =
  if i = String.length s then raise Not_found
  else
    match s.[i] with
    [ 'n' -> ('\n', i + 1)
    | 'r' -> ('\r', i + 1)
    | 't' -> ('\t', i + 1)
    | 'b' -> ('\b', i + 1)
    | '\\' -> ('\\', i + 1)
    | '"' -> ('"', i + 1)
    | ''' -> (''', i + 1)
    | '0'..'9' as c -> backslash1 (valch c) s (i + 1)
    | 'x' -> backslash1h s (i + 1)
    | _ -> raise Not_found ]
and backslash1 cod s i =
  if i = String.length s then ('\\', i - 1)
  else
    match s.[i] with
    [ '0'..'9' as c -> backslash2 (10 * cod + valch c) s (i + 1)
    | _ -> ('\\', i - 1) ]
and backslash2 cod s i =
  if i = String.length s then ('\\', i - 2)
  else
    match s.[i] with
    [ '0'..'9' as c -> (Char.chr (10 * cod + valch c), i + 1)
    | _ -> ('\\', i - 2) ]
and backslash1h s i =
  if i = String.length s then ('\\', i - 1)
  else
    match s.[i] with
    [ '0'..'9' as c -> backslash2h (valch c) s (i + 1)
    | 'a'..'f' as c -> backslash2h (valch_a c) s (i + 1)
    | 'A'..'F' as c -> backslash2h (valch_A c) s (i + 1)
    | _ -> ('\\', i - 1) ]
and backslash2h cod s i =
  if i = String.length s then ('\\', i - 2)
  else
    match s.[i] with
    [ '0'..'9' as c -> (Char.chr (16 * cod + valch c), i + 1)
    | 'a'..'f' as c -> (Char.chr (16 * cod + valch_a c), i + 1)
    | 'A'..'F' as c -> (Char.chr (16 * cod + valch_A c), i + 1)
    | _ -> ('\\', i - 2) ]
;

value rec skip_indent s i =
  if i = String.length s then i
  else
    match s.[i] with
    [ ' ' | '\t' -> skip_indent s (i + 1)
    | _ -> i ]
;

value skip_opt_linefeed s i =
  if i = String.length s then i else if s.[i] = '\010' then i + 1 else i
;

value eval_char s =
  if String.length s = 1 then s.[0]
  else if String.length s = 0 then failwith "invalid char token"
  else if s.[0] = '\\' then
    if String.length s = 2 && s.[1] = ''' then '''
    else
      try
        let (c, i) = backslash s 1 in
        if i = String.length s then c else raise Not_found
      with
      [ Not_found -> failwith "invalid char token" ]
  else failwith "invalid char token"
;

value eval_string loc s =
  bytes_to_string (loop 0 0) where rec loop len i =
    if i = String.length s then get_buff len
    else
      let (len, i) =
        if s.[i] = '\\' then
          let i = i + 1 in
          if i = String.length s then failwith "invalid string token"
          else if s.[i] = '"' then (store len '"', i + 1)
          else
            match s.[i] with
            [ '\010' -> (len, skip_indent s (i + 1))
            | '\013' -> (len, skip_indent s (skip_opt_linefeed s (i + 1)))
            | c ->
                try
                  let (c, i) = backslash s i in
                  (store len c, i)
                with
                [ Not_found -> (store (store len '\\') c, i + 1) ] ]
        else (store len s.[i], i + 1)
      in
      loop len i
;

value default_match =
  fun
  [ ("ANY", "") -> fun (con, prm) -> prm
  | ("ANY", v) ->
      fun (con, prm) -> if v = prm then v else raise Stream.Failure
  | (p_con, "") ->
      fun (con, prm) -> if con = p_con then prm else raise Stream.Failure
  | (p_con, p_prm) ->
      fun (con, prm) ->
        if con = p_con && prm = p_prm then prm else raise Stream.Failure ]
;

value input_file = ref "";
value line_nb = ref (ref 0);
value bol_pos = ref (ref 0);
value restore_lexing_info = ref None;

(* The lexing buffer used by pa_lexer.cmo *)

value rev_implode l =
  let s = string_create (List.length l) in
  bytes_to_string (loop (string_length s - 1) l) where rec loop i =
    fun
    [ [c :: l] -> do { string_unsafe_set s i c; loop (i - 1) l }
    | [] -> s ]
;

module Lexbuf :
  sig
    type t = 'abstract;
    value empty : t;
    value add : char -> t -> t;
    value get : t -> string;
  end =
  struct
    type t = list char;
    value empty = [];
    value add c l = [c :: l];
    value get = rev_implode;
  end
;
