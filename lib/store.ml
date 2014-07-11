(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** This module implements an "untyped store", in this particular case
    we see it as an extensible record whose fields are left
    unspecified. ***)

(** We use a dynamic "name" allocator. But if we needed to serialise
    stores, we might want something static to avoid troubles with
    plugins order. *)

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

  type t = Obj.t option array
(** Objects are accessed through an array access. *)

type 'a field = int

let max_length = 128
(** Ought to be enough for anybody. It has to be smaller that [Max_young_wosize]
    in order to fit into the minor heap, the latter being defined to 256 in
    OCaml. *)

let uset (obj : t) (i : 'a field) (v : 'a option) =
  (** We cast to integers in order not to use the costly [caml_modify]. This
      assumes that [obj] lives in the minor heap. *)
  let v : int = Obj.magic v in
  let obj : int array = Obj.magic obj in
  Array.unsafe_set obj i v

let allocate len : t =
  (** Returns an array filled with [None]. *)
  Obj.magic (Obj.new_block 0 len)

let empty : t = [||]

let set (s : t) (i : 'a field) (v : 'a) : t =
  let v = Some v in
  let len = Array.length s in
  let nlen = if i < len then len else succ i in
  let () = assert (0 < nlen && nlen <= max_length) in
  let ans = allocate nlen in
  (** Important: No more allocation from here. *)
  for i = 0 to pred len do
    uset ans i (Array.unsafe_get s i)
  done;
  uset ans i v;
  ans

let get (s : t) (i : 'a field) : 'a option =
  let len = Array.length s in
  if len <= i then None
  else Obj.magic (Array.unsafe_get s i)

let remove (s : t) (i : 'a field) =
  let len = Array.length s in
  let () = assert (0 <= i) in
  let ans = allocate len in
  (** Important: No more allocation from here. *)
  for i = 0 to pred len do
    uset ans i (Array.unsafe_get s i)
  done;
  if i < len then uset ans i None;
  ans

let merge (s1 : t) (s2 : t) : t =
  let len1 = Array.length s1 in
  let len2 = Array.length s2 in
  let nlen = if len1 < len2 then len2 else len1 in
  let ans = allocate nlen in
  (** Important: No more allocation from here. *)
  for i = 0 to pred len2 do
    uset ans i (Array.unsafe_get s2 i)
  done;
  for i = 0 to pred len1 do
    let v = Array.unsafe_get s1 i in
    match v with
    | None -> ()
    | Some _ -> uset ans i v
  done;
  ans

let field () = next ()

end
