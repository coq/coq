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

(** {1 Directory paths = section names paths } *)

(** Dirpaths are lists of module identifiers.
    The actual representation is reversed to optimise sharing:
    Coq.A.B is ["B";"A";"Coq"] *)

type module_ident = Id.t

let default_module_name = Id.of_string "If you see this, it's a bug"

type t = module_ident list

let compare = List.compare Id.compare
let equal = List.equal Id.equal

let rec hash accu = function
  | [] -> accu
  | id :: dp ->
    let accu = Hashset.Combine.combine (Id.hash id) accu in
    hash accu dp

let hash dp = hash 0 dp

let make x = x
let repr x = x

let empty = []

let is_empty = List.is_empty

let to_string = function
  | [] -> "<>"
  | sl -> String.concat "." (List.rev_map Id.to_string sl)

let print dp = Pp.str (to_string dp)

let initial = [default_module_name]

module Hdir = Hashcons.Hlist(Id)

let hcons = Hashcons.recursive_hcons Hdir.generate Hdir.hcons Id.hcons
