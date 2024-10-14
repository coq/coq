(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = string

type char63 = Uint63.t

(* Maximum length on a 32-bits system. *)
let max_length_int : int = 16777211

let max_length : Uint63.t = Uint63.of_int max_length_int

let to_string : t -> string = fun s -> s

let of_string : string -> t option = fun s ->
  if String.length s <= max_length_int then Some s else None

(* Return a string of size [max_length] if the parameter is too large.
   Use [c land 255] if [c] is not a valid character. *)
let make : Uint63.t -> char63 -> t = fun i c ->
  let i = Uint63.to_int_min i max_length_int in
  let c = Uint63.l_and c (Uint63.of_int 255) in
  let c = Char.chr (Uint63.to_int_min c 255) in
  String.make i c

let length : t -> Uint63.t = fun s ->
  Uint63.of_int (String.length s)

(* Out of bound access gives '\x00'. *)
let get : t -> Uint63.t -> char63 = fun s i ->
  let i = Uint63.to_int_min i max_length_int in
  if i < String.length s then
    Uint63.of_int (Char.code (String.get s i))
  else
    Uint63.zero

(* Returns an empty string if the [off] is out of bounds. If the [off] is
   in bounds, but there are less than [len] characters from this offset,
   the full suffix from [off] is returned. *)
let sub : t -> Uint63.t -> Uint63.t -> t = fun s off len ->
  let off = Uint63.to_int_min off max_int in
  let len = Uint63.to_int_min len max_int in
  let len_s = String.length s in
  if off < len_s then
    String.sub s off (min len (len_s - off))
  else
    ""

(* Only the longest possible prefix of [s2] is used, so that the resulting
   string satisfies the maximum length constraint. *)
let cat : t -> t -> t = fun s1 s2 ->
  let len1 = String.length s1 in
  let len2 = String.length s2 in
  if len1 + len2 <= max_length_int then
    s1 ^ s2
  else
    s1 ^ String.sub s2 0 (max_length_int - len1)

let compare : t -> t -> int =
  String.compare

let equal : t -> t -> bool =
  String.equal

let hash : t -> int =
  Hashtbl.hash

let unsafe_of_string : string -> t = fun s -> s

let compile : t -> string =
  Printf.sprintf "Pstring.unsafe_of_string %S"
