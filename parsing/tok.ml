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

let extract_string = function
  | KEYWORD s -> s
  | IDENT s -> s
  | STRING s -> s
  | PATTERNIDENT s -> s
  | FIELD s -> s
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

let of_pattern = function
  | "", s -> KEYWORD s
  | "IDENT", s -> IDENT s
  | "PATTERNIDENT", s -> PATTERNIDENT s
  | "FIELD", s -> FIELD s
  | "INT", s -> INT s
  | "STRING", s -> STRING s
  | "LEFTQMARK", _ -> LEFTQMARK
  | "BULLET", s -> BULLET s
  | "EOI", _ -> EOI
  | _ -> failwith "Tok.of_pattern: not a constructor"

let to_pattern = function
  | KEYWORD s -> "", s
  | IDENT s -> "IDENT", s
  | PATTERNIDENT s -> "PATTERNIDENT", s
  | FIELD s -> "FIELD", s
  | INT s -> "INT", s
  | STRING s -> "STRING", s
  | LEFTQMARK -> "LEFTQMARK", ""
  | BULLET s -> "BULLET", s
  | EOI -> "EOI", ""

let match_pattern =
  let err () = raise Stream.Failure in
  function
    | "", "" -> (function KEYWORD s -> s | _ -> err ())
    | "IDENT", "" -> (function IDENT s -> s | _ -> err ())
    | "PATTERNIDENT", "" -> (function PATTERNIDENT s -> s | _ -> err ())
    | "FIELD", "" -> (function FIELD s -> s | _ -> err ())
    | "INT", "" -> (function INT s -> s | _ -> err ())
    | "STRING", "" -> (function STRING s -> s | _ -> err ())
    | "LEFTQMARK", "" -> (function LEFTQMARK -> ""  | _ -> err ())
    | "BULLET", "" ->  (function BULLET s -> s  | _ -> err ())
    | "EOI", "" -> (function EOI -> "" | _ -> err ())
    | pat ->
	let tok = of_pattern pat in
	function tok' -> if equal tok tok' then snd pat else err ()
