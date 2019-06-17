(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module implements an "untyped store", in this particular case
    we see it as an extensible record whose fields are left
    unspecified. ***)

(** We use a dynamic "name" allocator. But if we needed to serialise
    stores, we might want something static to avoid troubles with
    plugins order. *)

module type S =
sig
  type t
  type 'a field
  val field : unit -> 'a field
  val empty : t
  val set : t -> 'a field -> 'a -> t
  val get : t -> 'a field -> 'a option
  val remove : t -> 'a field -> t
  val merge : t -> t -> t
end

module Make() : S =
struct
  module Dyn = Dyn.Make()
  module Map = Dyn.Map(struct type 'a t = 'a end)

  type t = Map.t
  type 'a field = 'a Dyn.tag

  let next = ref 0
  let field () =
    let f = Dyn.anonymous !next in
    incr next;
    f

  let empty =
    Map.empty
  let set s f v =
    Map.add f v s
  let get s f =
    try Some (Map.find f s)
    with Not_found -> None
  let remove s f =
    Map.remove f s
  let merge s1 s2 =
    Map.fold (fun (Map.Any (f, v)) s -> Map.add f v s) s1 s2
end
