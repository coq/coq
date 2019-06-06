(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of token for the Coq lexer and parser *)

let string_equal (s1 : string) s2 = s1 = s2

type 'c p =
  | PKEYWORD : string -> string p
  | PPATTERNIDENT : string option -> string p
  | PIDENT : string option -> string p
  | PFIELD : string option -> string p
  | PNUMERAL : NumTok.t option -> NumTok.t p
  | PSTRING : string option -> string p
  | PLEFTQMARK : unit p
  | PBULLET : string option -> string p
  | PQUOTATION : string -> string p
  | PEOI : unit p

let pattern_strings : type c. c p -> string * string option =
  function
  | PKEYWORD s -> "", Some s
  | PPATTERNIDENT s -> "PATTERNIDENT", s
  | PIDENT s -> "IDENT", s
  | PFIELD s -> "FIELD", s
  | PNUMERAL None -> "NUMERAL", None
  | PNUMERAL (Some n) -> "NUMERAL", Some (NumTok.to_string n)
  | PSTRING s -> "STRING", s
  | PLEFTQMARK -> "LEFTQMARK", None
  | PBULLET s -> "BULLET", s
  | PQUOTATION lbl -> "QUOTATION", Some lbl
  | PEOI -> "EOI", None

type t =
  | KEYWORD of string
  | PATTERNIDENT of string
  | IDENT of string
  | FIELD of string
  | NUMERAL of NumTok.t
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | QUOTATION of string * string
  | EOI

let equal_p (type a b) (t1 : a p) (t2 : b p) : (a, b) Util.eq option =
  let streq s1 s2 = match s1, s2 with None, None -> true
    | Some s1, Some s2 -> string_equal s1 s2 | _ -> false in
  match t1, t2 with
  | PKEYWORD s1, PKEYWORD s2 when string_equal s1 s2 -> Some Util.Refl
  | PPATTERNIDENT s1, PPATTERNIDENT s2 when streq s1 s2 -> Some Util.Refl
  | PIDENT s1, PIDENT s2 when streq s1 s2 -> Some Util.Refl
  | PFIELD s1, PFIELD s2 when streq s1 s2 -> Some Util.Refl
  | PNUMERAL None, PNUMERAL None -> Some Util.Refl
  | PNUMERAL (Some n1), PNUMERAL (Some n2) when NumTok.equal n1 n2 -> Some Util.Refl
  | PSTRING s1, PSTRING s2 when streq s1 s2 -> Some Util.Refl
  | PLEFTQMARK, PLEFTQMARK -> Some Util.Refl
  | PBULLET s1, PBULLET s2 when streq s1 s2 -> Some Util.Refl
  | PQUOTATION s1, PQUOTATION s2 when string_equal s1 s2 -> Some Util.Refl
  | PEOI, PEOI -> Some Util.Refl
  | _ -> None

let equal t1 t2 = match t1, t2 with
| IDENT s1, KEYWORD s2 -> string_equal s1 s2
| KEYWORD s1, KEYWORD s2 -> string_equal s1 s2
| PATTERNIDENT s1, PATTERNIDENT s2 -> string_equal s1 s2
| IDENT s1, IDENT s2 -> string_equal s1 s2
| FIELD s1, FIELD s2 -> string_equal s1 s2
| NUMERAL n1, NUMERAL n2 -> NumTok.equal n1 n2
| STRING s1, STRING s2 -> string_equal s1 s2
| LEFTQMARK, LEFTQMARK -> true
| BULLET s1, BULLET s2 -> string_equal s1 s2
| EOI, EOI -> true
| QUOTATION(s1,t1), QUOTATION(s2,t2) -> string_equal s1 s2 && string_equal t1 t2
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
  | NUMERAL n -> NumTok.to_string n
  | LEFTQMARK -> "?"
  | BULLET s -> s
  | QUOTATION(_,s) -> s
  | EOI -> ""

(* Invariant, txt is "ident" or a well parenthesized "{{....}}" *)
let trim_quotation txt =
  let len = String.length txt in
  if len = 0 then None, txt
  else
    let c = txt.[0] in
    if c = '(' || c = '[' || c = '{' then
      let rec aux n =
        if n < len && txt.[n] = c then aux (n+1)
        else Some c, String.sub txt n (len - (2*n))
      in
        aux 0
    else None, txt

let match_pattern (type c) (p : c p) : t -> c =
  let err () = raise Stream.Failure in
  let seq = string_equal in
  match p with
  | PKEYWORD s -> (function KEYWORD s' when seq s s' -> s' | NUMERAL n when seq s (NumTok.to_string n) -> s | _ -> err ())
  | PIDENT None -> (function IDENT s' -> s' | _ -> err ())
  | PIDENT (Some s) -> (function (IDENT s' | KEYWORD s') when seq s s' -> s' | _ -> err ())
  | PPATTERNIDENT None -> (function PATTERNIDENT s -> s | _ -> err ())
  | PPATTERNIDENT (Some s) -> (function PATTERNIDENT s' when seq s s' -> s' | _ -> err ())
  | PFIELD None -> (function FIELD s -> s | _ -> err ())
  | PFIELD (Some s) -> (function FIELD s' when seq s s' -> s' | _ -> err ())
  | PNUMERAL None -> (function NUMERAL s -> s | _ -> err ())
  | PNUMERAL (Some n) -> let s = NumTok.to_string n in (function NUMERAL n' when s = NumTok.to_string n' -> n' | _ -> err ())
  | PSTRING None -> (function STRING s -> s | _ -> err ())
  | PSTRING (Some s) -> (function STRING s' when seq s s' -> s' | _ -> err ())
  | PLEFTQMARK -> (function LEFTQMARK -> () | _ -> err ())
  | PBULLET None -> (function BULLET s -> s | _ -> err ())
  | PBULLET (Some s) -> (function BULLET s' when seq s s' -> s' | _ -> err ())
  | PQUOTATION lbl -> (function QUOTATION(lbl',s') when string_equal lbl lbl' -> s' | _ -> err ())
  | PEOI -> (function EOI -> () | _ -> err ())
