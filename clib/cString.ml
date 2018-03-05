(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type S = module type of String

module type ExtS =
sig
  include S
  [@@@ocaml.warning "-3"]     (* [@@noalloc] since 4.03.0 GPR#240 *)
  external equal : string -> string -> bool = "caml_string_equal" "noalloc"
  [@@@ocaml.warning "+3"]
  val hash : string -> int
  val is_empty : string -> bool
  val explode : string -> string list
  val implode : string list -> string
  val strip : string -> string
  val drop_simple_quotes : string -> string
  val string_index_from : string -> int -> string -> int
  val string_contains : where:string -> what:string -> bool
  val plural : int -> string -> string
  val conjugate_verb_to_be : int -> string
  val ordinal : int -> string
  val split : char -> string -> string list
  val is_sub : string -> string -> int -> bool
  module Set : Set.S with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set
  module List : CList.MonoS with type elt = t
  val hcons : string -> string
end

include String

[@@@ocaml.warning "-3"]     (* [@@noalloc] since 4.03.0 GPR#240 *)
external equal : string -> string -> bool = "caml_string_equal" "noalloc"
[@@@ocaml.warning "+3"]

let rec hash len s i accu =
  if i = len then accu
  else
    let c = Char.code (String.unsafe_get s i) in
    hash len s (succ i) (accu * 19 + c)

let hash s =
  let len = String.length s in
  hash len s 0 0

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

let is_empty s = String.length s = 0

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

let drop_simple_quotes s =
  let n = String.length s in
  if n > 2 && s.[0] = '\'' && s.[n-1] = '\'' then String.sub s 1 (n-2) else s

(* substring searching... *)

(* gdzie = where, co = what *)
(* gdzie=gdzie(string) gl=gdzie(length) gi=gdzie(index) *)
let rec raw_is_sub gdzie gl gi co cl ci =
  (ci>=cl) ||
  ((String.unsafe_get gdzie gi = String.unsafe_get co ci) &&
   (raw_is_sub gdzie gl (gi+1) co cl (ci+1)))

let rec raw_str_index i gdzie l c co cl =
  (* First adapt to ocaml 3.11 new semantics of index_from *)
  if (i+cl > l) then raise Not_found;
  (* Then proceed as in ocaml < 3.11 *)
  let i' = String.index_from gdzie i c in
    if (i'+cl <= l) && (raw_is_sub gdzie l i' co cl 0) then i' else
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

let is_sub p s off =
  let lp = String.length p in
  let ls = String.length s in
  if ls < off + lp then false
  else
    let rec aux i =
      if lp <= i then true
      else
        let cp = String.unsafe_get p i in
        let cs = String.unsafe_get s (off + i) in
        if cp = cs then aux (succ i) else false
    in
    aux 0

let plural n s = if n<>1 then s^"s" else s

let conjugate_verb_to_be n = if n<>1 then "are" else "is"

let ordinal n =
  let s =
    if (n / 10) mod 10 = 1 then "th"
    else match n mod 10 with
    | 1 -> "st"
    | 2 -> "nd"
    | 3 -> "rd"
    | _ -> "th"
  in
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

module Self =
struct
  type t = string
  let compare = compare
end

module Set = Set.Make(Self)
module Map = CMap.Make(Self)

module List = struct
  type elt = string
  let mem id l = List.exists (fun s -> equal id s) l
  let assoc id l = CList.assoc_f equal id l
  let remove_assoc id l = CList.remove_assoc_f equal id l
  let mem_assoc id l = List.exists (fun (a,_) -> equal id a) l
  let mem_assoc_sym id l = List.exists (fun (_,b) -> equal id b) l
  let equal l l' = CList.equal equal l l'
end

let hcons = Hashcons.simple_hcons Hashcons.Hstring.generate Hashcons.Hstring.hcons ()
