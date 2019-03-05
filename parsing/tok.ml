(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of token for the Coq lexer and parser *)

let string_equal (s1 : string) s2 = s1 = s2

type t =
  | KEYWORD of string
  | PATTERNIDENT of string
  | IDENT of string
  | FIELD of string
  | INT of string
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | EOI

let equal t1 t2 = match t1, t2 with
| IDENT s1, KEYWORD s2 -> string_equal s1 s2
| KEYWORD s1, KEYWORD s2 -> string_equal s1 s2
| PATTERNIDENT s1, PATTERNIDENT s2 -> string_equal s1 s2
| IDENT s1, IDENT s2 -> string_equal s1 s2
| FIELD s1, FIELD s2 -> string_equal s1 s2
| INT s1, INT s2 -> string_equal s1 s2
| STRING s1, STRING s2 -> string_equal s1 s2
| LEFTQMARK, LEFTQMARK -> true
| BULLET s1, BULLET s2 -> string_equal s1 s2
| EOI, EOI -> true
| _ -> false

let extract_string diff_mode = function
  | KEYWORD s -> s
  | IDENT s -> s
  | STRING s ->
    if diff_mode then
      let escape_quotes s =
        let len = String.length s in
        let buf = Buffer.create len in
        for i = 0 to len-1 do
          let ch = String.get s i in
          Buffer.add_char buf ch;
          if ch = '"' then Buffer.add_char buf '"' else ()
        done;
        Buffer.contents buf
      in
      "\"" ^ (escape_quotes s) ^ "\""
    else s
  | PATTERNIDENT s -> s
  | FIELD s -> if diff_mode then "." ^ s else s
  | INT s -> s
  | LEFTQMARK -> "?"
  | BULLET s -> s
  | EOI -> ""

let to_string = function
  | KEYWORD s -> Format.sprintf "%S" s
  | IDENT s -> Format.sprintf "IDENT %S" s
  | PATTERNIDENT s -> Format.sprintf "PATTERNIDENT %S" s
  | FIELD s -> Format.sprintf "FIELD %S" s
  | INT s -> Format.sprintf "INT %s" s
  | STRING s -> Format.sprintf "STRING %S" s
  | LEFTQMARK -> "LEFTQMARK"
  | BULLET s -> Format.sprintf "BULLET %S" s
  | EOI -> "EOI"

let match_keyword kwd = function
  | KEYWORD kwd' when kwd = kwd' -> true
  | _ -> false

(* Needed to fix Camlp5 signature.
 Cannot use Pp because of silly Tox -> Compat -> Pp dependency *)
let print ppf tok = Format.pp_print_string ppf (to_string tok)

(** For camlp5, conversion from/to [Plexing.pattern],
    and a match function analoguous to [Plexing.default_match] *)

type pattern = string * string option

let is_keyword = function
  | "", Some s -> Some s
  | _ -> None

let pattern_for_EOI = ("EOI",None)
let pattern_for_KEYWORD s = ("",Some s)
let pattern_for_IDENT s = ("IDENT",Some s)

let match_pattern (key, value) =
  let err () = raise Stream.Failure in
  let cond x =
    match value with
    | None -> x
    | Some value -> if string_equal value x then x else err () in
  match key with
  | "" -> (function { v = KEYWORD s } -> cond s | _ -> err ())
  | "IDENT" when value <> None -> (function { v = (IDENT s | KEYWORD s) } -> cond s | _ -> err ())
  | "IDENT" -> (function { v = IDENT s } -> cond s | _ -> err ())
  | "PATTERNIDENT" -> (function { v = PATTERNIDENT s } -> cond s | _ -> err ())
  | "FIELD" -> (function { v = FIELD s } -> cond s | _ -> err ())
  | "INT" -> (function { v = INT s } -> cond s | _ -> err ())
  | "STRING" -> (function { v = STRING s } -> cond s | _ -> err ())
  | "LEFTQMARK" -> (function { v = LEFTQMARK } -> cond "" | _ -> err ())
  | "BULLET" ->  (function { v = BULLET s } -> cond s  | _ -> err ())
  | "EOI" -> (function { v = EOI } -> cond "" | _ -> err ())
  | p -> CErrors.anomaly Pp.(str "Tok: unknown pattern " ++ str p)
