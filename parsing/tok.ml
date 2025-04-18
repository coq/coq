(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of token for the Rocq lexer and parser *)

let string_equal (s1 : string) s2 = s1 = s2

type 'c p =
  | PKEYWORD : string -> string p
  | PIDENT : string option -> string p
  | PFIELD : string option -> string p
  | PNUMBER : NumTok.Unsigned.t option -> NumTok.Unsigned.t p
  | PSTRING : string option -> string p
  | PLEFTQMARK : unit p
  | PBULLET : string option -> string p
  | PQUOTATION : string -> string p
  | PEOI : unit p

let pattern_strings : type c. c p -> string * string option =
  function
  | PKEYWORD s -> "", Some s
  | PIDENT s -> "IDENT", s
  | PFIELD s -> "FIELD", s
  | PNUMBER None -> "NUMBER", None
  | PNUMBER (Some n) -> "NUMBER", Some (NumTok.Unsigned.sprint n)
  | PSTRING s -> "STRING", s
  | PLEFTQMARK -> "LEFTQMARK", None
  | PBULLET s -> "BULLET", s
  | PQUOTATION lbl -> "QUOTATION", Some lbl
  | PEOI -> "EOI", None

type t =
  | KEYWORD of string
  | IDENT of string
  | FIELD of string
  | NUMBER of NumTok.Unsigned.t
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | QUOTATION of string * string
  | EOI

let equal_p (type a b) (t1 : a p) (t2 : b p) : (a, b) Util.eq option =
  let streq s1 s2 = match s1, s2 with None, None -> true
    | Some s1, Some s2 -> string_equal s1 s2 | _ -> false in
  match t1, t2 with
  | PIDENT s1, PIDENT s2 when streq s1 s2 -> Some Util.Refl
  | PKEYWORD s1, PKEYWORD s2 when string_equal s1 s2 -> Some Util.Refl
  | PIDENT (Some s1), PKEYWORD s2 when string_equal s1 s2 -> Some Util.Refl
  | PKEYWORD s1, PIDENT (Some s2) when string_equal s1 s2 -> Some Util.Refl
  | PFIELD s1, PFIELD s2 when streq s1 s2 -> Some Util.Refl
  | PNUMBER None, PNUMBER None -> Some Util.Refl
  | PNUMBER (Some n1), PNUMBER (Some n2) when NumTok.Unsigned.equal n1 n2 -> Some Util.Refl
  | PSTRING s1, PSTRING s2 when streq s1 s2 -> Some Util.Refl
  | PLEFTQMARK, PLEFTQMARK -> Some Util.Refl
  | PBULLET s1, PBULLET s2 when streq s1 s2 -> Some Util.Refl
  | PQUOTATION s1, PQUOTATION s2 when string_equal s1 s2 -> Some Util.Refl
  | PEOI, PEOI -> Some Util.Refl
  | _ -> None

let token_text : type c. c p -> string = function
  | PKEYWORD t -> "'" ^ t ^ "'"
  | PIDENT None -> "identifier"
  | PIDENT (Some t) -> "'" ^ t ^ "'"
  | PNUMBER None -> "number"
  | PNUMBER (Some n) -> "'" ^ NumTok.Unsigned.sprint n ^ "'"
  | PSTRING None -> "string"
  | PSTRING (Some s) -> "STRING \"" ^ s ^ "\""
  | PLEFTQMARK -> "LEFTQMARK"
  | PEOI -> "end of input"
  | PFIELD None -> "FIELD"
  | PFIELD (Some s) -> "FIELD \"" ^ s ^ "\""
  | PBULLET None -> "BULLET"
  | PBULLET (Some s) -> "BULLET \"" ^ s ^ "\""
  | PQUOTATION lbl -> "QUOTATION \"" ^ lbl ^ "\""

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
  | FIELD s -> if diff_mode then "." ^ s else s
  | NUMBER n -> NumTok.Unsigned.sprint n
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

type ast =
| Akeyword of string
| Aident of string
| Apatternident of string
| Afield of string
| Anumber of NumTok.Unsigned.t
| Astring of string
| Aleftqmark
| Abullet of string
| Aquotation of string * string
| Aeoi

let ast_to_string = function
  | Akeyword(s) -> "\"" ^ String.escaped s ^ "\""
  | Aident(s) -> "\"" ^ String.escaped s ^ "\""
  | Apatternident(s) -> "\"" ^ String.escaped s ^ "\""
  | Afield(s) -> "\"" ^ String.escaped s ^ "\""
  | Anumber(s) -> NumTok.Unsigned.sprint s
  | Astring(s) -> "\"" ^ String.escaped s ^ "\""
  | Aleftqmark -> "\"?\""
  | Abullet(s) -> "\"" ^ String.escaped s ^ "\""
  | Aquotation(lbl, s) -> Format.sprintf "(quotation \"%s\" \"%s\")" (String.escaped lbl) (String.escaped s)
  | Aeoi -> "(eoi)"

let match_pattern (type c) (p : c p) : t -> ast * c =
  let err () = raise Gramlib.Stream.Failure in
  let seq = string_equal in
  match p with
  | PKEYWORD s -> (function KEYWORD s' when seq s s' -> (Akeyword s, s)
                          | NUMBER n when seq s (NumTok.Unsigned.sprint n) -> (Akeyword s, s)
                          | STRING s' when seq s (CString.quote_coq_string s') -> (Akeyword s, s)
                          | _ -> err ())
  | PIDENT None -> (function IDENT s' -> (Aident s', s') | _ -> err ())
  | PIDENT (Some s) -> (function (IDENT s' | KEYWORD s') when seq s s' -> (Aident s, s') | _ -> err ())
  | PFIELD None -> (function FIELD s -> (Afield s, s) | _ -> err ())
  | PFIELD (Some s) -> (function FIELD s' when seq s s' -> (Afield s, s') | _ -> err ())
  | PNUMBER None -> (function NUMBER s -> (Anumber s, s) | _ -> err ())
  | PNUMBER (Some n) -> let s = NumTok.Unsigned.sprint n in (function NUMBER n' when s = NumTok.Unsigned.sprint n' -> (Anumber n', n') | _ -> err ())
  | PSTRING None -> (function STRING s -> (Astring s, s) | _ -> err ())
  | PSTRING (Some s) -> (function STRING s' when seq s s' -> (Astring s, s') | _ -> err ())
  | PLEFTQMARK -> (function LEFTQMARK -> (Aleftqmark, ()) | _ -> err ())
  | PBULLET None -> (function BULLET s -> (Abullet s, s) | _ -> err ())
  | PBULLET (Some s) -> (function BULLET s' when seq s s' -> (Abullet s, s') | _ -> err ())
  | PQUOTATION lbl -> (function QUOTATION(lbl',s') when string_equal lbl lbl' -> (Aquotation(lbl, s'), s') | _ -> err ())
  | PEOI -> (function EOI -> (Aeoi, ()) | _ -> err ())
