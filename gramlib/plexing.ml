(* camlp5r *)
(* plexing.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Versdep

type pattern = string * string

exception Error of string

type location = Ploc.t
type location_function = int -> location
type 'te lexer_func = char Stream.t -> 'te Stream.t * location_function

type 'te lexer =
  { tok_func : 'te lexer_func;
    tok_using : pattern -> unit;
    tok_removing : pattern -> unit;
    mutable tok_match : pattern -> 'te -> string;
    tok_text : pattern -> string;
    mutable tok_comm : location list option }

let make_loc = Ploc.make_unlined
let dummy_loc = Ploc.dummy

let lexer_text (con, prm) =
  if con = "" then "'" ^ prm ^ "'"
  else if prm = "" then con
  else con ^ " '" ^ prm ^ "'"

let locerr () = failwith "Lexer: location function"
let loct_create () = ref (array_create 1024 None), ref false
let loct_func (loct, ov) i =
  match
    if i < 0 || i >= Array.length !loct then
      if !ov then Some dummy_loc else None
    else Array.unsafe_get !loct i
  with
    Some loc -> loc
  | None -> locerr ()
let loct_add (loct, ov) i loc =
  if i >= Array.length !loct then
    let new_tmax = Array.length !loct * 2 in
    if new_tmax < Sys.max_array_length then
      let new_loct = array_create new_tmax None in
      Array.blit !loct 0 new_loct 0 (Array.length !loct);
      loct := new_loct;
      !loct.(i) <- Some loc
    else ov := true
  else !loct.(i) <- Some loc

let make_stream_and_location next_token_loc =
  let loct = loct_create () in
  let ts =
    Stream.from
      (fun i ->
         let (tok, loc) = next_token_loc () in loct_add loct i loc; Some tok)
  in
  ts, loct_func loct

let lexer_func_of_parser next_token_loc cs =
  let line_nb = ref 1 in
  let bolpos = ref 0 in
  make_stream_and_location (fun () -> next_token_loc (cs, line_nb, bolpos))

let lexer_func_of_ocamllex lexfun cs =
  let lb =
    Lexing.from_function
      (fun s n ->
         try string_set s 0 (Stream.next cs); 1 with Stream.Failure -> 0)
  in
  let next_token_loc _ =
    let tok = lexfun lb in
    let loc = make_loc (Lexing.lexeme_start lb, Lexing.lexeme_end lb) in
    tok, loc
  in
  make_stream_and_location next_token_loc

(* Char and string tokens to real chars and string *)

let buff = ref (string_create 80)
let store len x =
  if len >= string_length !buff then
    buff := string_cat !buff (string_create (string_length !buff));
  string_set !buff len x;
  succ len
let get_buff len = string_sub !buff 0 len

let valch x = Char.code x - Char.code '0'
let valch_a x = Char.code x - Char.code 'a' + 10
let valch_A x = Char.code x - Char.code 'A' + 10

let rec backslash s i =
  if i = String.length s then raise Not_found
  else
    match s.[i] with
      'n' -> '\n', i + 1
    | 'r' -> '\r', i + 1
    | 't' -> '\t', i + 1
    | 'b' -> '\b', i + 1
    | '\\' -> '\\', i + 1
    | '"' -> '"', i + 1
    | '\'' -> '\'', i + 1
    | '0'..'9' as c -> backslash1 (valch c) s (i + 1)
    | 'x' -> backslash1h s (i + 1)
    | _ -> raise Not_found
and backslash1 cod s i =
  if i = String.length s then '\\', i - 1
  else
    match s.[i] with
      '0'..'9' as c -> backslash2 (10 * cod + valch c) s (i + 1)
    | _ -> '\\', i - 1
and backslash2 cod s i =
  if i = String.length s then '\\', i - 2
  else
    match s.[i] with
      '0'..'9' as c -> Char.chr (10 * cod + valch c), i + 1
    | _ -> '\\', i - 2
and backslash1h s i =
  if i = String.length s then '\\', i - 1
  else
    match s.[i] with
      '0'..'9' as c -> backslash2h (valch c) s (i + 1)
    | 'a'..'f' as c -> backslash2h (valch_a c) s (i + 1)
    | 'A'..'F' as c -> backslash2h (valch_A c) s (i + 1)
    | _ -> '\\', i - 1
and backslash2h cod s i =
  if i = String.length s then '\\', i - 2
  else
    match s.[i] with
      '0'..'9' as c -> Char.chr (16 * cod + valch c), i + 1
    | 'a'..'f' as c -> Char.chr (16 * cod + valch_a c), i + 1
    | 'A'..'F' as c -> Char.chr (16 * cod + valch_A c), i + 1
    | _ -> '\\', i - 2

let rec skip_indent s i =
  if i = String.length s then i
  else
    match s.[i] with
      ' ' | '\t' -> skip_indent s (i + 1)
    | _ -> i

let skip_opt_linefeed s i =
  if i = String.length s then i else if s.[i] = '\010' then i + 1 else i

let eval_char s =
  if String.length s = 1 then s.[0]
  else if String.length s = 0 then failwith "invalid char token"
  else if s.[0] = '\\' then
    if String.length s = 2 && s.[1] = '\'' then '\''
    else
      try
        let (c, i) = backslash s 1 in
        if i = String.length s then c else raise Not_found
      with Not_found -> failwith "invalid char token"
  else failwith "invalid char token"

let eval_string loc s =
  let rec loop len i =
    if i = String.length s then get_buff len
    else
      let (len, i) =
        if s.[i] = '\\' then
          let i = i + 1 in
          if i = String.length s then failwith "invalid string token"
          else if s.[i] = '"' then store len '"', i + 1
          else
            match s.[i] with
              '\010' -> len, skip_indent s (i + 1)
            | '\013' -> len, skip_indent s (skip_opt_linefeed s (i + 1))
            | c ->
                try let (c, i) = backslash s i in store len c, i with
                  Not_found -> store (store len '\\') c, i + 1
        else store len s.[i], i + 1
      in
      loop len i
  in
  bytes_to_string (loop 0 0)

let default_match =
  function
    "ANY", "" -> (fun (con, prm) -> prm)
  | "ANY", v ->
      (fun (con, prm) -> if v = prm then v else raise Stream.Failure)
  | p_con, "" ->
      (fun (con, prm) -> if con = p_con then prm else raise Stream.Failure)
  | p_con, p_prm ->
      fun (con, prm) ->
        if con = p_con && prm = p_prm then prm else raise Stream.Failure

let input_file = ref ""
let line_nb = ref (ref 0)
let bol_pos = ref (ref 0)
let restore_lexing_info = ref None

(* The lexing buffer used by pa_lexer.cmo *)

let rev_implode l =
  let s = string_create (List.length l) in
  let rec loop i =
    function
      c :: l -> string_unsafe_set s i c; loop (i - 1) l
    | [] -> s
  in
  bytes_to_string (loop (string_length s - 1) l)

module Lexbuf :
  sig
    type t
    val empty : t
    val add : char -> t -> t
    val get : t -> string
  end =
  struct
    type t = char list
    let empty = []
    let add c l = c :: l
    let get = rev_implode
  end
