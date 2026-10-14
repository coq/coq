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

type (_,_) exact =
  | Any : ('a,'a) exact
  | Exact : 'a -> ('a,unit) exact

let is_exact (type a b) : (a,b) exact -> bool = function
  | Any -> false
  | Exact _ -> true

let exact_eq (type a b b') (eq:a -> a -> bool) (a:(a,b) exact) (b:(a,b') exact) : (b,b') Util.eq option =
  match a, b with
  | Any, Any -> Some Refl
  | Exact a, Exact b -> if eq a b then Some Refl else None
  | (Any | Exact _), _ -> None

type 'c p =
  | PKEYWORD : string -> unit p
  | PIDENT : (string,'v) exact -> 'v p
  | PFIELD : string option -> string p
  | PNUMBER : NumTok.Unsigned.t option -> NumTok.Unsigned.t p
  | PSTRING : string option -> string p
  | PLEFTQMARK : unit p
  | PBULLET : string option -> string p
  | PQUOTATION : string -> string p
  | PEOI : unit p

let pattern_exact : type c. c p -> bool = function
  | PKEYWORD _ -> true
  | PIDENT id -> is_exact id
  | PFIELD s -> Option.has_some s
  | PNUMBER n -> Option.has_some n
  | PSTRING s -> Option.has_some s
  | PLEFTQMARK -> false
  | PBULLET s -> Option.has_some s
  | PQUOTATION _ -> true
  | PEOI -> false

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
  | PIDENT s1, PIDENT s2 ->
    begin match exact_eq string_equal s1 s2 with Some Refl -> Some Util.Refl | None -> None end
  | PKEYWORD s1, PKEYWORD s2 when string_equal s1 s2 -> Some Util.Refl
  | PIDENT (Exact s1), PKEYWORD s2 when string_equal s1 s2 -> Some Util.Refl
  | PKEYWORD s1, PIDENT (Exact s2) when string_equal s1 s2 -> Some Util.Refl
  | PFIELD s1, PFIELD s2 when streq s1 s2 -> Some Util.Refl
  | PNUMBER None, PNUMBER None -> Some Util.Refl
  | PNUMBER (Some n1), PNUMBER (Some n2) when NumTok.Unsigned.equal n1 n2 -> Some Util.Refl
  | PSTRING s1, PSTRING s2 when streq s1 s2 -> Some Util.Refl
  | PLEFTQMARK, PLEFTQMARK -> Some Util.Refl
  | PBULLET s1, PBULLET s2 when streq s1 s2 -> Some Util.Refl
  | PQUOTATION s1, PQUOTATION s2 when string_equal s1 s2 -> Some Util.Refl
  | PEOI, PEOI -> Some Util.Refl
  | _ -> None

let compare_p (type a b) (t1 : a p) (t2 : b p) : int =
  match t1, t2 with
  | PIDENT Any, PIDENT Any -> 0
  | PIDENT Any, _ -> -1
  | _, PIDENT Any -> 1
  | (PIDENT (Exact s1) | PKEYWORD s1), (PIDENT (Exact s2) | PKEYWORD s2) -> String.compare s1 s2
  | (PIDENT (Exact _) | PKEYWORD _), _ -> -1
  | _, (PIDENT (Exact _) | PKEYWORD _) -> 1
  | PFIELD s1, PFIELD s2 -> Option.compare String.compare s1 s2
  | PFIELD _, _ -> -1
  | _, PFIELD _ -> 1
  | PNUMBER n1, PNUMBER n2 -> Option.compare NumTok.Unsigned.compare n1 n2
  | PNUMBER _, _ -> -1
  | _, PNUMBER _ -> 1
  | PSTRING s1, PSTRING s2 -> Option.compare String.compare s1 s2
  | PSTRING _, _ -> -1
  | _, PSTRING _ -> 1
  | PLEFTQMARK, PLEFTQMARK -> 0
  | PLEFTQMARK, _ -> -1
  | _, PLEFTQMARK -> 1
  | PBULLET s1, PBULLET s2 -> Option.compare String.compare s1 s2
  | PBULLET _, _ -> -1
  | _, PBULLET _ -> 1
  | PQUOTATION s1, PQUOTATION s2 -> String.compare s1 s2
  | PQUOTATION _, _ -> -1
  | _, PQUOTATION _ -> 1
  | PEOI, PEOI -> 0

let token_text : type c. c p -> string = function
  | PKEYWORD t -> "'" ^ t ^ "'"
  | PIDENT Any -> "identifier"
  | PIDENT (Exact t) -> "'" ^ t ^ "'"
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

let match_pattern (type c) (p : c p) : t -> c option =
  let seq = string_equal in
  match p with
  | PKEYWORD s ->
    (function KEYWORD s' when seq s s' -> Some ()
            | NUMBER n when seq s (NumTok.Unsigned.sprint n) -> Some ()
            | STRING s' when seq s (CString.quote_coq_string s') -> Some ()
            | _ -> None)
  | PIDENT Any -> (function IDENT s' -> Some s' | _ -> None)
  | PIDENT (Exact s) -> (function (IDENT s' | KEYWORD s') when seq s s' -> Some () | _ -> None)
  | PFIELD None -> (function FIELD s -> Some s| _ -> None)
  | PFIELD (Some s) -> (function FIELD s' when seq s s' -> Some s' | _ -> None)
  | PNUMBER None -> (function NUMBER s -> Some s| _ -> None)
  | PNUMBER (Some n) ->
    (function NUMBER n' when NumTok.Unsigned.equal n n' -> Some n' | _ -> None)
  | PSTRING None -> (function STRING s -> Some s | _ -> None)
  | PSTRING (Some s) -> (function STRING s' when seq s s' -> Some s' | _ -> None)
  | PLEFTQMARK -> (function LEFTQMARK -> Some () | _ -> None)
  | PBULLET None -> (function BULLET s -> Some s | _ -> None)
  | PBULLET (Some s) -> (function BULLET s' when seq s s' -> Some s' | _ -> None)
  | PQUOTATION lbl -> (function QUOTATION(lbl',s') when string_equal lbl lbl' -> Some s' | _ -> None)
  | PEOI -> (function EOI -> Some () | _ -> None)
