(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*** This module implements an "untyped store", in this particular case we
        see it as an extensible record whose fields are left unspecified. ***)

(* We give a short implementation of a universal type. This is mostly equivalent
    to what is proposed by module Dyn.ml, except that it requires no explicit tag. *)

(* We use a dynamic "name" allocator. But if we needed to serialise stores, we
might want something static to avoid troubles with plugins order. *)

module type T =
sig
end

module type S =
sig
  type t
  type 'a field
  val empty : t
  val set : t -> 'a field -> 'a -> t
  val get : t -> 'a field -> 'a option
  val remove : t -> 'a field -> t
  val merge : t -> t -> t
  val field : unit -> 'a field
end

module Make (M : T) : S =
struct

let next =
  let count = ref 0 in fun () ->
  let n = !count in
  incr count;
  n

type t = Obj.t Int.Map.t

type 'a field = int

let empty = Int.Map.empty

let set s (id : 'a field) (x : 'a) = Int.Map.add id (Obj.repr x) s

let get s (id : 'a field) : 'a option =
  try Some (Obj.obj (Int.Map.find id s))
  with Not_found -> None

let remove s (id : 'a field) =
  Int.Map.remove id s

let merge s1 s2 =
  Int.Map.fold Int.Map.add s1 s2

let field () = next ()

end
