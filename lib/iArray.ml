(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

module type US =
sig
  type +'a t
  (** We put it covariant even though it isn't, as we're going to use it purely
      functionnaly. *)
  val length : 'a t -> int
  val create : int -> 'a t
  val copy : 'a t -> 'a t
  val get : 'a t -> int -> 'a
  val set : 'a t -> int -> 'a -> unit
end
(** Minimal signature of unsafe arrays *)

module ObjArray =
struct
  type +'a t = Obj.t

  type dummy = int option
  (** We choose this type such that:
      1. It is not a float, not to trigger the float unboxing mechanism
      2. It is not a scalar, to ensure calling of the caml_copy function,
        otherwise that may result in strange GC behaviour.
  *)

  let length = Obj.size
  let create len = Obj.new_block 0 len
  let copy obj = Obj.dup obj

  let get (obj : 'a t) i : 'a =
    let obj : dummy array = Obj.magic obj in
    let ans = Array.unsafe_get obj i in
    Obj.magic ans

  let set (obj : 'a t) i (x : 'a) =
    let x : dummy = Obj.magic x in
    let obj : dummy array = Obj.magic obj in
    Array.unsafe_set obj i x
end

module Make(M : US) =
struct

type +'a t = 'a M.t

let length = M.length

let get t i =
  if i < 0 || M.length t <= i then
    invalid_arg "Array.get"
  else
    M.get t i

(* let set t i x =
  if i < 0 || M.length t <= i then
    invalid_arg "Array.set"
  else
    M.set t i x *)

let make len x =
  let ans = M.create len in
  let () =
    for i = 0 to pred len do
      M.set ans i x
    done
  in
  ans

let copy = M.copy

let init len f =
  let ans = M.create len in
  let () =
    for i = 0 to pred len do
      M.set ans i (f i)
    done
  in
  ans

let append t1 t2 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let ans = M.create (len1 + len2) in
  let () =
    for i = 0 to pred len1 do
      M.set ans i (M.get t1 i)
    done
  in
  let () =
    for i = 0 to pred len2 do
      M.set ans (len1 + i) (M.get t2 i)
    done
  in
  ans

let concat l =
  let rec len accu = function
  | [] -> accu
  | t :: l -> len (M.length t + accu) l
  in
  let len = len 0 l in
  let ans = M.create len in
  let rec iter off = function
  | [] -> ()
  | t :: l ->
    let len = M.length t in
    let () =
      for i = 0 to pred len do
        M.set ans (off + i) (M.get t i)
      done
    in
    iter (off + len) l
  in
  let () = iter 0 l in
  ans

let sub t off len =
  let tlen = M.length t in
  let () = if off < 0 || off + len > tlen then
    invalid_arg "Array.sub"
  in
  let ans = M.create len in
  let () =
    for i = 0 to len - 1 do
      M.set ans i (M.get t (off + i))
    done
  in
  ans

let of_list l =
  let len = List.length l in
  let ans = M.create len in
  let rec iter off = function
  | [] -> ()
  | x :: l ->
    let () = M.set ans off x in
    iter (succ off) l
  in
  let () = iter 0 l in
  ans

let to_list t =
  let rec iter off accu =
    if off < 0 then accu
    else iter (pred off) (M.get t off :: accu)
  in
  iter (M.length t - 1) []

let iter f t =
  for i = 0 to M.length t - 1 do
    f (M.get t i)
  done

let iteri f t =
  for i = 0 to M.length t - 1 do
    f i (M.get t i)
  done

let map f t =
  let len = M.length t in
  let ans = M.create len in
  let () =
    for i = 0 to pred len do
      M.set ans i (f (M.get t i))
    done
  in
  ans

let mapi f t =
  let len = M.length t in
  let ans = M.create len in
  let () =
    for i = 0 to pred len do
      M.set ans i (f i (M.get t i))
    done
  in
  ans

let fold_right f accu t =
  let rec fold i accu =
    if i < 0 then accu
    else fold (pred i) (f (M.get t i) accu)
  in
  fold (M.length t - 1) accu

let fold_left f accu t =
  let len = M.length t in
  let rec fold i accu =
    if len <= i then accu
    else fold (succ i) (f accu (M.get t i))
  in
  fold 0 accu

end

module M = Make(ObjArray)

include M

module Unsafe =
struct

let get = ObjArray.get

let set = ObjArray.set

let of_array (t : 'a array) : 'a ObjArray.t =
  let tag = Obj.tag (Obj.repr t) in
  let () = if tag = Obj.double_array_tag then
    invalid_arg "Array.of_array"
  in
  Obj.magic t

let to_array (t : 'a ObjArray.t) : 'a array =
  if Obj.size t = 0 then [||]
  else
    let dummy = Obj.field t 0 in
    let () = if Obj.tag dummy = Obj.double_tag then
      invalid_arg "Array.to_array"
    in
    Obj.magic t

end
