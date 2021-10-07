(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

type t = string

let equal = String.equal

let compare = String.compare

let hash = String.hash

let check_valid ?(strict=true) x =
  let iter (fatal, x) = if fatal || strict then CErrors.user_err Pp.(str x) in
  Option.iter iter (Unicode.ident_refutation x)

let is_valid s = match Unicode.ident_refutation s with
  | None -> true
  | Some _ -> false

let is_valid_ident_part s = match Unicode.ident_refutation ("x"^s) with
  | None -> true
  | Some _ -> false

let of_bytes s =
  let s = Bytes.to_string s in
  check_valid s;
  String.hcons s

let of_string s =
  let () = check_valid s in
  String.hcons s

let of_string_soft s =
  let () = check_valid ~strict:false s in
  String.hcons s

let to_string id = id

let print id = Pp.str id

module Self =
struct
  type t = string
  let compare = compare
end

module Set = Set.Make(Self)
module Map = CMap.Make(Self)

module Pred = Predicate.Make(Self)

module List = String.List

let hcons = String.hcons
