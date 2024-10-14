(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = int
let initial = 1
let dummy = 0
let fresh =
  let cur = ref initial in
  fun () -> incr cur; !cur
let to_string = string_of_int
let of_int id = id
let to_int id = id
let newer_than id1 id2 = id1 > id2

let state_id_info : (t * t) Exninfo.t = Exninfo.make "stateid"
let add exn ~valid id =
  Exninfo.add exn state_id_info (valid, id)
let get exn = Exninfo.get exn state_id_info

let equal = Int.equal
let compare = Int.compare

let print id = Pp.int id

module Self = struct
 type t = int
 let compare = compare
end

module Set = Set.Make(Self)

type exn_info = { id : t; valid : t }

type ('a,'b) request = {
  exn_info : exn_info;
  stop : t;
  document : 'b;
  loc : Loc.t option;
  uuid     : 'a;
  name     : string
}

let is_valid_ref = ref (fun ~doc:_ (_ : t) -> true)
let is_valid ~doc id = !is_valid_ref ~doc id
let set_is_valid f = is_valid_ref := f
