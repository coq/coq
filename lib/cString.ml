(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** FIXME: use module type of *)
module type S =
sig
  external length : string -> int = "%string_length"
  external get : string -> int -> char = "%string_safe_get"
  external set : string -> int -> char -> unit = "%string_safe_set"
  external create : int -> string = "caml_create_string"
  val make : int -> char -> string
  val copy : string -> string
  val sub : string -> int -> int -> string
  val fill : string -> int -> int -> char -> unit
  val blit : string -> int -> string -> int -> int -> unit
  val concat : string -> string list -> string
  val iter : (char -> unit) -> string -> unit
  val escaped : string -> string
  val index : string -> char -> int
  val rindex : string -> char -> int
  val index_from : string -> int -> char -> int
  val rindex_from : string -> int -> char -> int
  val contains : string -> char -> bool
  val contains_from : string -> int -> char -> bool
  val rcontains_from : string -> int -> char -> bool
  val uppercase : string -> string
  val lowercase : string -> string
  val capitalize : string -> string
  val uncapitalize : string -> string
  type t = string
  val compare: t -> t -> int
  external unsafe_get : string -> int -> char = "%string_unsafe_get"
  external unsafe_set : string -> int -> char -> unit = "%string_unsafe_set"
  external unsafe_blit :
    string -> int -> string -> int -> int -> unit = "caml_blit_string" "noalloc"
  external unsafe_fill :
    string -> int -> int -> char -> unit = "caml_fill_string" "noalloc"
end

module type ExtS =
sig
  include S
  external equal : string -> string -> bool = "caml_string_equal" "noalloc"
  val explode : string -> string list
  val implode : string list -> string
  val strip : string -> string
  val map : (char -> char) -> string -> string
  val drop_simple_quotes : string -> string
  val string_index_from : string -> int -> string -> int
  val string_contains : where:string -> what:string -> bool
  val plural : int -> string -> string
  val ordinal : int -> string
  val split : char -> string -> string list
end

include String

external equal : string -> string -> bool = "caml_string_equal" "noalloc"

let explode s =
  let rec explode_rec n =
    if n >= String.length s then
      []
    else
      String.make 1 (String.get s n) :: explode_rec (succ n)
  in
  explode_rec 0

let implode sl = String.concat "" sl

let is_blank = function
  | ' ' | '\r' | '\t' | '\n' -> true
  | _ -> false

let strip s =
  let n = String.length s in
  let rec lstrip_rec i =
    if i < n && is_blank s.[i] then
      lstrip_rec (i+1)
    else i
  in
  let rec rstrip_rec i =
    if i >= 0 && is_blank s.[i] then
      rstrip_rec (i-1)
    else i
  in
  let a = lstrip_rec 0 and b = rstrip_rec (n-1) in
  String.sub s a (b-a+1)

let map f s =
  let l = String.length s in
  let r = String.create l in
  for i = 0 to (l - 1) do r.[i] <- f (s.[i]) done;
  r

let drop_simple_quotes s =
  let n = String.length s in
  if n > 2 & s.[0] = '\'' & s.[n-1] = '\'' then String.sub s 1 (n-2) else s

(* substring searching... *)

(* gdzie = where, co = what *)
(* gdzie=gdzie(string) gl=gdzie(length) gi=gdzie(index) *)
let rec is_sub gdzie gl gi co cl ci =
  (ci>=cl) ||
  ((String.unsafe_get gdzie gi = String.unsafe_get co ci) &&
   (is_sub gdzie gl (gi+1) co cl (ci+1)))

let rec raw_str_index i gdzie l c co cl =
  (* First adapt to ocaml 3.11 new semantics of index_from *)
  if (i+cl > l) then raise Not_found;
  (* Then proceed as in ocaml < 3.11 *)
  let i' = String.index_from gdzie i c in
    if (i'+cl <= l) && (is_sub gdzie l i' co cl 0) then i' else
      raw_str_index (i'+1) gdzie l c co cl

let string_index_from gdzie i co =
  if co="" then i else
    raw_str_index i gdzie (String.length gdzie)
      (String.unsafe_get co 0) co (String.length co)

let string_contains ~where ~what =
  try
    let _ = string_index_from where 0 what in true
  with
      Not_found -> false

let plural n s = if n<>1 then s^"s" else s

let ordinal n =
  let s = match n mod 10 with 1 -> "st" | 2 -> "nd" | 3 -> "rd" | _ -> "th" in
  string_of_int n ^ s

(* string parsing *)

let split c s =
  let len = String.length s in
  let rec split n =
    try
      let pos = String.index_from s n c in
      let dir = String.sub s n (pos-n) in
      dir :: split (succ pos)
    with
      | Not_found -> [String.sub s n (len-n)]
  in
  if Int.equal len 0 then [] else split 0
