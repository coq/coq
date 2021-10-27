(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* In OCaml, arrays of double are unboxed (Obj.double_array_tag), we
   cannot do that with primitive arrays and primitive floats since in
   Coq, primitive floats can be open terms and it is not possible to
   mix unboxed floats and pointers to open terms in an array (TODO:
   link to bug in test-suite).
   We must then rewrite most array primitives to ensure arrays of floats
   are boxed. *)
module Array = struct
  let length = Array.length
  let unsafe_get = Array.unsafe_get
  let unsafe_set = Array.unsafe_set
  let fold_left = Array.fold_left
  let fold_left2 = CArray.fold_left2

  let make n def =
    if Obj.(tag (repr def) != double_tag) then Array.make n def else
      let a = Array.make n (Obj.magic 0) in
      for i = 0 to n - 1 do a.(i) <- def done;
      a

  let init n f =
    if n <= 0 then Array.init n f else
      let a = make n (f 0) in
      for i = 1 to n - 1 do a.(i) <- f i done;
      a

  let copy a =
    let n = length a in
    if n <= 0 || Obj.(tag (repr a) != double_array_tag) then Array.copy a else
      let a' = make n a.(0) in
      for i = 1 to n - 1 do a'.(i) <- a.(i) done;
      a'

  let map f a =
    let n = length a in
    if n <= 0 then Array.map f a else
      let a' = make n (f a.(0)) in
      for i = 1 to n - 1 do a'.(i) <- f a.(i) done;
      a'
end

let max_array_length32 = 4194303

let max_length = Uint63.of_int max_array_length32

let length_to_int i = snd (Uint63.to_int2 i)

let trunc_size n =
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int max_array_length32) then
    length_to_int n
  else max_array_length32

type 'a t = ('a kind) ref
and 'a kind =
  | Array of 'a array * 'a
  | Updated of int * 'a * 'a t

let unsafe_of_array t def = ref (Array (t,def))
let of_array t def = unsafe_of_array (Array.copy t) def

let rec rerootk t k =
  match !t with
  | Array (a, _) -> k a
  | Updated (i, v, p) ->
      let k' a =
        let v' = Array.unsafe_get a i in
        Array.unsafe_set a i v;
        t := !p; (* i.e., Array (a, def) *)
        p := Updated (i, v', t);
        k a in
      rerootk p k'

let reroot t = rerootk t (fun a -> a)

let length_int p =
  Array.length (reroot p)

let length p = Uint63.of_int @@ length_int p

let get p n =
  let t = reroot p in
  let l = Array.length t in
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
    Array.unsafe_get t (length_to_int n)
  else
    match !p with
    | Array (_, def) -> def
    | Updated _ -> assert false

let set p n e =
  let a = reroot p in
  let l = Uint63.of_int (Array.length a) in
  if Uint63.le Uint63.zero n && Uint63.lt n l then
    let i = length_to_int n in
    let v' = Array.unsafe_get a i in
    Array.unsafe_set a i e;
    let t = ref !p in (* i.e., Array (a, def) *)
    p := Updated (i, v', t);
    t
  else p

let default p =
  let _ = reroot p in
  match !p with
  | Array (_,def) -> def
  | Updated _ -> assert false

let make n def =
  ref (Array (Array.make (trunc_size n) def, def))

let init n f def =
  let n = trunc_size n in
  let t = Array.init n f in
  ref (Array (t, def))

let to_array p =
  let _ = reroot p in
  match !p with
  | Array (t,def) -> Array.copy t, def
  | Updated _ -> assert false

let copy p =
  let (t,def) = to_array p in
  ref (Array (t,def))

let reroot t =
  let _ = reroot t in
  t

let map f p =
  let p = reroot p in
  match !p with
  | Array (t,def) -> ref (Array (Array.map f t, f def))
  | Updated _ -> assert false

let fold_left f x p =
  let p = reroot p in
  match !p with
  | Array (t,def) -> f (Array.fold_left f x t) def
  | Updated _ -> assert false

let fold_left2 f a p1 p2 =
  let p1 = reroot p1 in
  let p2 = reroot p2 in
  match !p1, !p2 with
  | Array (t1, def1), Array (t2, def2) ->
    f (Array.fold_left2 f a t1 t2) def1 def2
  | _ -> assert false
