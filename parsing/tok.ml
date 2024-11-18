(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of token for the Coq lexer and parser *)

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

let has_payload : type a. a p -> bool =
  function
  | PKEYWORD s -> true
  | PIDENT s | PFIELD s | PSTRING s | PBULLET s ->
    Option.has_some s
  | PNUMBER s -> Option.has_some s
  | PLEFTQMARK -> false
  | PQUOTATION _ -> true
  | PEOI -> false

let classify : type a. a p -> Gramlib.Plexing.classifier =
  let open Gramlib.Plexing in
  function
  | PKEYWORD s -> Keyword s
  | PIDENT s -> Other ("IDENT", s)
  | PFIELD s -> Other ("FIELD", s)
  | PNUMBER None -> Other ("NUMBER", None)
  | PNUMBER (Some n) -> Other ("NUMBER", Some (NumTok.Unsigned.sprint n))
  | PSTRING s -> Other ("STRING", s)
  | PLEFTQMARK -> Other ("LEFTQMARK", None)
  | PBULLET s -> Other ("BULLET", s)
  | PQUOTATION lbl -> Other ("QUOTATION", Some lbl)
  | PEOI -> Other ("EOI", None)

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

let stringeq (type a) s1 s2 : (a, a) CSig.iseq =
  if string_equal s1 s2 then CSig.IsRefl else CSig.IsNone

let streq (type a) s1 s2 : (a, a) CSig.iseq = match s1, s2 with
| None, None -> CSig.IsRefl
| Some s1, Some s2 -> stringeq s1 s2
| None, Some _ | Some _, None -> CSig.IsNone

let equal_p (type a b) (t1 : a p) (t2 : b p) : (a, b) CSig.iseq =
  match t1, t2 with
  | PIDENT s1, PIDENT s2 -> streq s1 s2
  | PKEYWORD s1, PKEYWORD s2 -> stringeq s1 s2
  | PIDENT (Some s1), PKEYWORD s2 -> stringeq s1 s2
  | PKEYWORD s1, PIDENT (Some s2) -> stringeq s1 s2
  | PFIELD s1, PFIELD s2 -> streq s1 s2
  | PNUMBER None, PNUMBER None -> CSig.IsRefl
  | PNUMBER (Some n1), PNUMBER (Some n2) -> if NumTok.Unsigned.equal n1 n2 then CSig.IsRefl else CSig.IsNone
  | PSTRING s1, PSTRING s2 -> streq s1 s2
  | PLEFTQMARK, PLEFTQMARK -> CSig.IsRefl
  | PBULLET s1, PBULLET s2 -> streq s1 s2
  | PQUOTATION s1, PQUOTATION s2 -> stringeq s1 s2
  | PEOI, PEOI -> CSig.IsRefl
  | _ -> CSig.IsNone

let equal t1 t2 = match t1, t2 with
  | IDENT s1, KEYWORD s2 -> string_equal s1 s2
  | KEYWORD s1, KEYWORD s2 -> string_equal s1 s2
  | IDENT s1, IDENT s2 -> string_equal s1 s2
  | FIELD s1, FIELD s2 -> string_equal s1 s2
  | NUMBER n1, NUMBER n2 -> NumTok.Unsigned.equal n1 n2
  | STRING s1, STRING s2 -> string_equal s1 s2
  | LEFTQMARK, LEFTQMARK -> true
  | BULLET s1, BULLET s2 -> string_equal s1 s2
  | EOI, EOI -> true
  | QUOTATION(s1,t1), QUOTATION(s2,t2) -> string_equal s1 s2 && string_equal t1 t2
  | _ -> false

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

let match_pattern (type c) (p : c p) : t -> c =
  let err () = raise Gramlib.Stream.Failure in
  let seq = string_equal in
  match p with
  | PKEYWORD s -> (function KEYWORD s' when seq s s' -> s'
                          | NUMBER n when seq s (NumTok.Unsigned.sprint n) -> s
                          | STRING s' when seq s (CString.quote_coq_string s') -> s
                          | _ -> err ())
  | PIDENT None -> (function IDENT s' -> s' | _ -> err ())
  | PIDENT (Some s) -> (function (IDENT s' | KEYWORD s') when seq s s' -> s' | _ -> err ())
  | PFIELD None -> (function FIELD s -> s | _ -> err ())
  | PFIELD (Some s) -> (function FIELD s' when seq s s' -> s' | _ -> err ())
  | PNUMBER None -> (function NUMBER s -> s | _ -> err ())
  | PNUMBER (Some n) -> let s = NumTok.Unsigned.sprint n in (function NUMBER n' when s = NumTok.Unsigned.sprint n' -> n' | _ -> err ())
  | PSTRING None -> (function STRING s -> s | _ -> err ())
  | PSTRING (Some s) -> (function STRING s' when seq s s' -> s' | _ -> err ())
  | PLEFTQMARK -> (function LEFTQMARK -> () | _ -> err ())
  | PBULLET None -> (function BULLET s -> s | _ -> err ())
  | PBULLET (Some s) -> (function BULLET s' when seq s s' -> s' | _ -> err ())
  | PQUOTATION lbl -> (function QUOTATION(lbl',s') when string_equal lbl lbl' -> s' | _ -> err ())
  | PEOI -> (function EOI -> () | _ -> err ())
