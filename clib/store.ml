(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
  val empty : t
  val set : t -> 'a field -> 'a -> t
  val get : t -> 'a field -> 'a option
  val remove : t -> 'a field -> t
  val merge : t -> t -> t
  val field : unit -> 'a field
end

module Make () : S =
struct

  let next =
    let count = ref 0 in fun () ->
      let n = !count in
      incr count;
      n

  type t = Obj.t option array
  (** Store are represented as arrays. For small values, which is typicial,
      is slightly quicker than other implementations. *)

type 'a field = int

let allocate len : t = Array.make len None

let empty : t = [||]

let set (s : t) (i : 'a field) (v : 'a) : t =
  let len = Array.length s in
  let nlen = if i < len then len else succ i in
  let () = assert (0 <= i) in
  let ans = allocate nlen in
  Array.blit s 0 ans 0 len;
  Array.unsafe_set ans i (Some (Obj.repr v));
  ans

let get (s : t) (i : 'a field) : 'a option =
  let len = Array.length s in
  if len <= i then None
  else Obj.magic (Array.unsafe_get s i)

let remove (s : t) (i : 'a field) =
  let len = Array.length s in
  let () = assert (0 <= i) in
  let ans = allocate len in
  Array.blit s 0 ans 0 len;
  if i < len then Array.unsafe_set ans i None;
  ans

let merge (s1 : t) (s2 : t) : t =
  let len1 = Array.length s1 in
  let len2 = Array.length s2 in
  let nlen = if len1 < len2 then len2 else len1 in
  let ans = allocate nlen in
  (** Important: No more allocation from here. *)
  Array.blit s2 0 ans 0 len2;
  for i = 0 to pred len1 do
    let v = Array.unsafe_get s1 i in
    match v with
    | None -> ()
    | Some _ -> Array.unsafe_set ans i v
  done;
  ans

let field () = next ()

end
