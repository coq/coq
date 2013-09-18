(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type t = int

let repr x = x
let unsafe_of_int x = x
let compare = Int.compare
let equal = Int.equal

module Self =
struct
  type _t = t
  type t = _t
  let compare = compare
end

module Set = Set.Make(Self)
module Map = CMap.Make(Self)
