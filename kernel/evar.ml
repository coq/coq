(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Internal = struct
type t = int

let repr x = x
let unsafe_of_int x = x
let compare = Int.compare
let equal = Int.equal
let hash = Int.hash
let print x = Pp.(str "?X" ++ int x)

module Set = Int.Set
module Map = Int.Map
end

module Public = Internal
include Public
