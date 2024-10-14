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

let repr x = x
let unsafe_of_int x = x
let compare = Int.compare
let equal = Int.equal
let hash = Int.hash
let print x = Pp.(str "?X" ++ int x)

module Set = Int.Set
module Map = Int.Map
