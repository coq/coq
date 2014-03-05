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
      functionally. *)
  val length : 'a t -> int
  val create : int -> 'a t
  val copy : 'a t -> 'a t
  val get : 'a t -> int -> 'a
  val set : 'a t -> int -> 'a -> unit
  val safe_get : 'a t -> int -> 'a
  val safe_set : 'a t -> int -> 'a -> unit
end
(** Minimal signature of unsafe arrays *)

module ObjArray : US =
struct
  type +'a t = Obj.t

  type dummy = int option
  (** We choose this type such that:
      1. It is not a float, not to trigger the float unboxing mechanism
      2. It is not a scalar, to ensure calling of the caml_modify function,
        otherwise that may result in strange GC behaviour.
  *)

  let length obj =
    let obj : dummy array = Obj.magic obj in
    Array.length obj

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

  let safe_get (obj : 'a t) i : 'a =
    let obj : dummy array = Obj.magic obj in
    let ans = Array.get obj i in
    Obj.magic ans

  let safe_set (obj : 'a t) i (x : 'a) =
    let x : dummy = Obj.magic x in
    let obj : dummy array = Obj.magic obj in
    Array.set obj i x

end

module M = ObjArray

type +'a t = 'a M.t

let length = M.length

let get = M.safe_get

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

let is_empty t = M.length t = 0

(* let copy = M.copy *)

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
    invalid_arg "IArray.sub"
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

(** ITERS *)

let iter f t =
  for i = 0 to M.length t - 1 do
    f (M.get t i)
  done

let iteri f t =
  for i = 0 to M.length t - 1 do
    f i (M.get t i)
  done

(** MAPS *)

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

let map2 f t1 t2 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let () = if len1 <> len2 then invalid_arg "IArray.map2" in
  let ans = M.create len1 in
  for i = 0 to len1 do
    M.set ans i (f (M.get t1 i) (M.get t2 i));
  done;
  ans

let map2i f t1 t2 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let () = if len1 <> len2 then invalid_arg "IArray.map2i" in
  let ans = M.create len1 in
  for i = 0 to len1 do
    M.set ans i (f i (M.get t1 i) (M.get t2 i));
  done;
  ans

let map3 f t1 t2 t3 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let len3 = M.length t3 in
  let () = if len1 <> len2 || len1 <> len3 then invalid_arg "IArray.map3" in
  let ans = M.create len1 in
  for i = 0 to len1 do
    M.set ans i (f (M.get t1 i) (M.get t2 i) (M.get t3 i));
  done;
  ans

let smartmap f t =
  let len = M.length t in
  let rec loop i =
    if i = len then t
    else
      let x = M.get t i in
      let y = f x in
      if x == y then loop (succ i)
      (* We have to do it by hand *)
      else begin
        let ans = M.create len in
        for j = 0 to pred i do
          M.set ans j (M.get t j)
        done;
        M.set ans i y;
        for j = succ i to pred len do
          M.set ans i (f (M.get t i))
        done;
        ans
      end
  in
  loop 0

(** FOLDS *)

let fold_right f t accu =
  let rec fold i accu =
    if i < 0 then accu
    else fold (pred i) (f (M.get t i) accu)
  in
  fold (M.length t - 1) accu

let fold_right2 f t1 t2 accu =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let () = if len1 <> len2 then invalid_arg "IArray.fold_right2" in
  let rec fold i accu =
    if i < 0 then accu
    else fold (pred i) (f (M.get t1 i) (M.get t2 i) accu)
  in
  fold (len1 - 1) accu

let fold_left f accu t =
  let len = M.length t in
  let rec fold i accu =
    if len <= i then accu
    else fold (succ i) (f accu (M.get t i))
  in
  fold 0 accu

let fold_lefti f accu t =
  let len = M.length t in
  let rec fold i accu =
    if len <= i then accu
    else fold (succ i) (f i accu (M.get t i))
  in
  fold 0 accu

let fold_left2 f accu t1 t2 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let () = if len1 <> len2 then invalid_arg "IArray.fold_left2" in
  let rec fold i accu =
    if len1 <= i then accu
    else fold (succ i) (f accu (M.get t1 i) (M.get t2 i))
  in
  fold 0 accu

let fold_left2i f accu t1 t2 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let () = if len1 <> len2 then invalid_arg "IArray.fold_left2" in
  let rec fold i accu =
    if len1 <= i then accu
    else fold (succ i) (f i accu (M.get t1 i) (M.get t2 i))
  in
  fold 0 accu

(** FORALL *)

let for_all f t =
  let len = M.length t in
  let rec loop i =
    if i = len then true
    else f (M.get t i) && loop (succ i)
  in
  loop 0

let for_all2 f t1 t2 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let () = if len1 <> len2 then invalid_arg "IArray.fold_left2" in
  let rec loop i =
    if i = len1 then true
    else f (M.get t1 i) (M.get t2 i) && loop (succ i)
  in
  loop 0

(** EXISTS *)

let exists f t =
  let len = M.length t in
  let rec loop i =
    if i = len then false
    else f (M.get t i) || loop (succ i)
  in
  loop 0

(** OTHERS *)

let compare f t1 t2 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let c = Pervasives.compare len1 len2 in
  let rec loop i =
    if i = len1 then 0
    else
      let x1 = M.get t1 i in
      let x2 = M.get t2 i in
      let c = f x1 x2 in
      if c = 0 then loop (succ i)
      else c
  in
  if c = 0 then loop 0
  else c

let equal f t1 t2 =
  let len1 = M.length t1 in
  let len2 = M.length t2 in
  let rec loop i =
    if i = len1 then true
    else
      let x1 = M.get t1 i in
      let x2 = M.get t2 i in
      f x1 x2 && loop (succ i)
  in
  if len1 = len2 then loop 0
  else false

let of_array t =
  let len = Array.length t in
  let ans = M.create len in
  for i = 0 to pred len do
    M.set ans i (Array.unsafe_get t i)
  done;
  ans

let to_array t =
  let init i = M.get t i in
  Array.init (M.length t) init

(** Purely functional equivalents *)

let set t i x =
  let ans = M.copy t in
  let () = M.safe_set t i x in
  ans

let fill t off len x =
  let tlen = M.length t in
  let () =
    if off < 0 || len < 0 || off > tlen - len
    then invalid_arg "IArray.fill"
  in
  let ans = M.create tlen in
  for i = 0 to pred off do
    M.set ans i (M.get t i)
  done;
  for i = off to off + len - 1 do
    M.set t i x
  done;
  for i = off + len to pred tlen do
    M.set ans i (M.get t i)
  done;
  ans

let blit src soff dst doff len =
  let slen = M.length src in
  let dlen = M.length dst in
  let () =
    if len < 0 || soff < 0 || soff > slen - len ||
      doff < 0 || doff > dlen - len
    then invalid_arg "IArray.blit"
  in
  let ans = M.create dlen in
  for i = 0 to pred doff do
    M.set ans i (M.get dst i)
  done;
  for i = 0 to pred len do
    M.set ans (doff + i) (M.get src (soff + i))
  done;
  for i = doff + len to pred dlen do
    M.set ans i (M.get dst i)
  done;
  ans

(** Specific *)

let empty = M.create 0

let singleton x = make 1 x

let diff t = function
| [] -> t
| l ->
  let ans = M.copy t in
  let iter (i, x) = M.safe_set ans i x in
  let () = List.iter iter l in
  ans

(* end *)

(* module M = Make(ObjArray) *)

(* include M *)

module Unsafe =
struct

let get = M.get

let of_array (t : 'a array) : 'a M.t =
  let tag = Obj.tag (Obj.repr t) in
  let () = if tag = Obj.double_array_tag then
    invalid_arg "IArray.of_array"
  in
  Obj.magic t

let to_array (t : 'a M.t) : 'a array =
  if Obj.size (Obj.repr t) = 0 then [||]
  else
    let dummy = Obj.field (Obj.repr t) 0 in
    let () = if Obj.tag dummy = Obj.double_tag then
      invalid_arg "IArray.to_array"
    in
    Obj.magic t

end
