(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type t = int

external equal : int -> int -> bool = "%eq"

external compare : int -> int -> int = "caml_int_compare"

let hash i = i land 0x3FFFFFFF

module Self =
struct
  type t = int
  let compare = compare
end

module Set = Set.Make(Self)
module Map =
struct
  include CMap.Make(Self)

  type 'a map = 'a CMap.Make(Self).t

  type 'a _map =
  | MEmpty
  | MNode of 'a map * int * 'a * 'a map * int

  let map_prj : 'a map -> 'a _map = Obj.magic

  let rec find i s = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode (l, k, v, r, h) ->
    if i < k then find i l
    else if i = k then v
    else find i r
end

module List = struct
  let mem = List.memq
  let assoc = List.assq
  let mem_assoc = List.mem_assq
  let remove_assoc = List.remove_assq
end
