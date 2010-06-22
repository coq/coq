(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The type of token for the Coq lexer and parser *)

type t =
  | KEYWORD of string
  | METAIDENT of string
  | PATTERNIDENT of string
  | IDENT of string
  | FIELD of string
  | INT of string
  | STRING of string
  | LEFTQMARK
  | EOI

let extract_string = function
  | KEYWORD s -> s
  | IDENT s -> s
  | STRING s -> s
  | METAIDENT s -> s
  | PATTERNIDENT s -> s
  | FIELD s -> s
  | INT s -> s
  | LEFTQMARK -> "?"
  | EOI -> ""

let to_string = function
  | KEYWORD s -> Format.sprintf "%S" s
  | IDENT s -> Format.sprintf "IDENT %S" s
  | METAIDENT s -> Format.sprintf "METAIDENT %S" s
  | PATTERNIDENT s -> Format.sprintf "PATTERNIDENT %S" s
  | FIELD s -> Format.sprintf "FIELD %S" s
  | INT s -> Format.sprintf "INT %s" s
  | STRING s -> Format.sprintf "STRING %S" s
  | LEFTQMARK -> "LEFTQMARK"
  | EOI -> "EOI"

let match_keyword kwd = function
  | KEYWORD kwd' when kwd = kwd' -> true
  | _ -> false

let print ppf tok = Format.fprintf ppf "%s" (to_string tok)

(** For camlp5, conversion from/to [Plexing.pattern],
    and a match function analoguous to [Plexing.default_match] *)

let of_pattern = function
  | "", s -> KEYWORD s
  | "IDENT", s -> IDENT s
  | "METAIDENT", s -> METAIDENT s
  | "PATTERNIDENT", s -> PATTERNIDENT s
  | "FIELD", s -> FIELD s
  | "INT", s -> INT s
  | "STRING", s -> STRING s
  | "LEFTQMARK", _ -> LEFTQMARK
  | "EOI", _ -> EOI
  | _ -> failwith "Tok.of_pattern: not a constructor"

let to_pattern = function
  | KEYWORD s -> "", s
  | IDENT s -> "IDENT", s
  | METAIDENT s -> "METAIDENT", s
  | PATTERNIDENT s -> "PATTERNIDENT", s
  | FIELD s -> "FIELD", s
  | INT s -> "INT", s
  | STRING s -> "STRING", s
  | LEFTQMARK -> "LEFTQMARK", ""
  | EOI -> "EOI", ""

let match_pattern =
  let err () = raise Stream.Failure in
  function
    | "", "" -> (function KEYWORD s -> s | _ -> err ())
    | "IDENT", "" -> (function IDENT s -> s | _ -> err ())
    | "METAIDENT", "" -> (function METAIDENT s -> s | _ -> err ())
    | "PATTERNIDENT", "" -> (function PATTERNIDENT s -> s | _ -> err ())
    | "FIELD", "" -> (function FIELD s -> s | _ -> err ())
    | "INT", "" -> (function INT s -> s | _ -> err ())
    | "STRING", "" -> (function STRING s -> s | _ -> err ())
    | "LEFTQMARK", "" -> (function LEFTQMARK -> ""  | _ -> err ())
    | "EOI", "" -> (function EOI -> "" | _ -> err ())
    | pat ->
	let tok = of_pattern pat in
	function tok' -> if tok = tok' then snd pat else err ()
