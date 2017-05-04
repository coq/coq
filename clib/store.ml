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

  type 'a merge_arg =
    | One of 'a
    | Both of 'a * 'a

  type 'a merge_field = 'a merge_arg -> 'a option
  type 'a field
  val empty : t
  val set : t -> 'a field -> 'a -> t
  val get : t -> 'a field -> 'a option
  val remove : t -> 'a field -> t
  val merge : t -> t -> t
  val field : 'a merge_field -> 'a field
  val default_merge_field : 'a merge_field
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


  type 'a merge_arg =
    | One of 'a
    | Both of 'a * 'a

  type 'a merge_field = 'a merge_arg -> 'a option

  type 'a field = int

let allocate len : t = Array.make len None

let merge_fns = ref (Array.make 10 (Obj.magic (fun _ _ -> None)))
(** Merge functions are declared for all fields of the store. The merge
    function array is global for all store objects of this type and grows
    monotonically with each new field declaration. *)

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
  let merge i x y =
    let fn = Array.unsafe_get !merge_fns i in
    let fn : 'a merge_field = Obj.magic fn in
    match x, y with
    | Some x, Some y -> fn (Both (x, y))
    | Some x, None -> fn (One x)
    | None, Some y -> fn (One y)
    | None, None -> None
  in
  for i = 0 to pred nlen do
    let v1 = if i < len1 then Array.unsafe_get s1 i else None in
    let v2 = if i < len2 then Array.unsafe_get s2 i else None in
    Array.unsafe_set ans i (merge i v1 v2)
  done;
  ans

let field merge =
  let i = next () in
  let () =
    (** Extend merge array if too small *)
    let init = !merge_fns in
    let len = Array.length init in
    if i < len then ()
    else begin
      let arr = allocate (len + 1) in
      Array.blit init 0 arr 0 len;
      merge_fns := arr
    end
  in
  Array.set !merge_fns i (Obj.magic merge);
  i

let default_merge_field xy =
  match xy with
  | One x | Both (x, _) -> Some x

end
