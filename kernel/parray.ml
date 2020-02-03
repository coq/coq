(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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

let rec length_int p =
  match !p with
  | Array (t,_) -> Array.length t
  | Updated (_, _, p) -> length_int p

let length p = Uint63.of_int @@ length_int p

let rec get p n =
  match !p with
  | Array (t,def) ->
      let l = Array.length t in
      if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
        Array.unsafe_get t (length_to_int n)
      else def
  | Updated (k,e,p) ->
     if Uint63.equal n (Uint63.of_int k) then e
     else get p n

let set p n e =
  let kind = !p in
  match kind with
  | Array (t,_) ->
      let l = Uint63.of_int @@ Array.length t in
      if Uint63.le Uint63.zero n && Uint63.lt n l then
        let res = ref kind in
        let n = length_to_int n in
        p := Updated (n, Array.unsafe_get t n, res);
        Array.unsafe_set t n e;
        res
      else p
  | Updated _ ->
      if Uint63.le Uint63.zero n && Uint63.lt n (length p) then
        ref (Updated((length_to_int n), e, p))
      else p

let rec default p =
  match !p with
  | Array (_,def) -> def
  | Updated (_,_,p) -> default p

let make n def =
  ref (Array (Array.make (trunc_size n) def, def))

let init n f def =
  let n = trunc_size n in
  let t = Array.init n f in
  ref (Array (t, def))

let rec to_array p =
  match !p with
  | Array (t,def) -> Array.copy t, def
  | Updated (n,e,p) ->
      let (t,_) as r = to_array p in
      Array.unsafe_set t n e; r

let copy p =
  let (t,def) = to_array p in
  ref (Array (t,def))

let rec rerootk t k =
  match !t with
  | Array _ -> k ()
  | Updated (i, v, t') ->
      let k' () =
        begin match !t' with
        | Array (a,_def) as n ->
            let v' = a.(i) in
            Array.unsafe_set a i v;
            t := n;
            t' := Updated (i, v', t)
        | Updated _ -> assert false
        end; k() in
      rerootk t' k'

let reroot t = rerootk t (fun () -> t)

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
    f (CArray.fold_left2 f a t1 t2) def1 def2
  | _ -> assert false
