(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Pp

module type S =
sig
type 'a tag
type t = Dyn : 'a tag * 'a -> t

val create : string -> 'a tag
val eq : 'a tag -> 'b tag -> ('a, 'b) CSig.eq option
val repr : 'a tag -> string
val dump : unit -> (int * string) list
end

module Make(M : CSig.EmptyS) =
struct
(* Dynamics, programmed with DANGER !!! *)

type 'a tag = int

type t = Dyn : 'a tag * 'a -> t

let dyntab = ref (Int.Map.empty : string Int.Map.t)
(** Instead of working with tags as strings, which are costly, we use their
    hash. We ensure unicity of the hash in the [create] function. If ever a
    collision occurs, which is unlikely, it is sufficient to tweak the offending
    dynamic tag. *)

let create (s : string) =
  let hash = Hashtbl.hash s in
  let () =
    if Int.Map.mem hash !dyntab then
      let old = Int.Map.find hash !dyntab in
      let msg = str "Dynamic tag collision: " ++ str s ++ str " vs. " ++ str old in
      anomaly ~label:"Dyn.create" msg
  in
  let () = dyntab := Int.Map.add hash s !dyntab in
  hash

let eq : 'a 'b. 'a tag -> 'b tag -> ('a, 'b) CSig.eq option =
  fun h1 h2 -> if Int.equal h1 h2 then Some (Obj.magic CSig.Refl) else None

let repr s =
  try Int.Map.find s !dyntab
  with Not_found ->
    anomaly (str "Unknown dynamic tag " ++ int s)

let dump () = Int.Map.bindings !dyntab

end