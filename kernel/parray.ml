(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Uniform Arrays: non-flat arrays (even floats are boxed, i.e., doesn't use
    {!Obj.double_array_tag}) *)
module UArray :
sig
  type 'a t
  val empty : 'a t
  val unsafe_get : 'a t -> int -> 'a
  val unsafe_set : 'a t -> int -> 'a -> unit
  val length : 'a t -> int
  val make : int -> 'a -> 'a t
  val copy : 'a t -> 'a t
  val of_array : 'a array -> 'a t
  val to_array : 'a t -> 'a array
  (* 'a should not be float (no Obj.double_tag) *)
  val unsafe_of_obj : Obj.t -> 'a t
end =
struct
  type 'a t = Obj.t array
  (** Guaranteed to be a non-flat array and no funny business with write
      barriers because of the opacity of Obj.t. *)

  let empty = [||]

  let length (v : 'a t) = Array.length v

  let of_array v =
    if (Obj.tag (Obj.repr v) == Obj.double_array_tag) then begin
      let n = Array.length v in
      (* Ensure that we initialize it with a non-float *)
      let ans = Array.make n (Obj.repr ()) in
      for i = 0 to n - 1 do
        Array.unsafe_set ans i (Obj.repr (Array.unsafe_get v i))
      done;
      ans
    end else
      (Obj.magic (Array.copy v))

  let obj_is_float x = Obj.tag x == Obj.double_tag

  let to_array (type a) (v : a t) : a array =
    let () = assert (not (Array.exists obj_is_float v)) in
    Obj.magic (Array.copy v)

  let unsafe_of_obj (type a) (v : Obj.t) =
    let () = assert (Obj.tag v == 0) in
    (Obj.obj v : a t)

  let unsafe_get = Obj.magic Array.unsafe_get
  let unsafe_set = Obj.magic Array.unsafe_set

  let make (type a) n (x : a) : a t =
    (* Ensure that we initialize it with a non-float *)
    let ans = Array.make n (Obj.repr ()) in
    let () = Array.fill ans 0 n (Obj.repr x) in
    ans

  let copy = Array.copy

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
  | Array of 'a UArray.t * 'a
  | Updated of int * 'a * 'a t

let unsafe_of_obj t def = ref (Array (UArray.unsafe_of_obj t, def))
let of_array t def = ref (Array (UArray.of_array t, def))

let rec rerootk t k =
  match !t with
  | Array (a, _) -> k a
  | Updated (i, v, p) ->
      let k' a =
        let v' = UArray.unsafe_get a i in
        UArray.unsafe_set a i v;
        t := !p; (* i.e., Array (a, def) *)
        p := Updated (i, v', t);
        k a in
      rerootk p k'

let reroot t = rerootk t (fun a -> a)

let length_int p =
  UArray.length (reroot p)

let length p = Uint63.of_int @@ length_int p

let get p n =
  let t = reroot p in
  let l = UArray.length t in
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
    UArray.unsafe_get t (length_to_int n)
  else
    match !p with
    | Array (_, def) -> def
    | Updated _ -> assert false

let set p n e =
  let a = reroot p in
  let l = Uint63.of_int (UArray.length a) in
  if Uint63.le Uint63.zero n && Uint63.lt n l then
    let i = length_to_int n in
    let v' = UArray.unsafe_get a i in
    UArray.unsafe_set a i e;
    let t = ref !p in (* i.e., Array (a, def) *)
    p := Updated (i, v', t);
    t
  else p

let default p =
  let _ = reroot p in
  match !p with
  | Array (_,def) -> def
  | Updated _ -> assert false

let make_int n def =
  ref (Array (UArray.make n def, def))

let make n def = make_int (trunc_size n) def

let uinit n f =
  if Int.equal n 0 then UArray.empty
  else begin
    let t = UArray.make n (f 0) in
    for i = 1 to n - 1 do
      UArray.unsafe_set t i (f i)
    done;
    t
  end

let init n f def =
  let n = trunc_size n in
  let t = uinit n f in
  ref (Array (t, def))

let to_array p =
  let _ = reroot p in
  match !p with
  | Array (t,def) -> UArray.to_array t, def
  | Updated _ -> assert false

let copy p =
  let _ = reroot p in
  match !p with
  | Array (t, def) -> ref (Array (UArray.copy t, def))
  | Updated _ -> assert false

(* Higher order combinators: the callback may update the underlying
   array requiring a reroot between each call. To avoid doing n
   reroots (-> O(n^2)), we copy if we have to reroot again. *)

let is_rooted p = match !p with
  | Array _ -> true
  | Updated _ -> false

let map f p =
  let t = reroot p in
  let len = UArray.length t in
  if Int.equal len 0 then make_int 0 (f (default p))
  else
    let res = UArray.make len (f (UArray.unsafe_get t 0)) in
    let t = ref t in
    let rerooted_again = ref false in
    let check_rooted () = if not !rerooted_again && not (is_rooted p)
      then (t := UArray.copy (reroot p); rerooted_again := true)
    in
    for i = 1 to len - 1 do
      check_rooted ();
      UArray.unsafe_set res i (f (UArray.unsafe_get !t i))
    done;
    let def = f (default p) in
    ref (Array (res, def))

let fold_left f x p =
  let r = ref x in
  let t = ref (reroot p) in
  let len = UArray.length !t in
  let rerooted_again = ref false in
  let check_rooted () = if not !rerooted_again && not (is_rooted p)
    then (t := UArray.copy (reroot p); rerooted_again := true)
  in
  for i = 0 to len - 1 do
    check_rooted ();
    r := f !r (UArray.unsafe_get !t i)
  done;
  f !r (default p)

let fold_left2 f a p1 p2 =
  let r = ref a in
  let t1 = ref (reroot p1) in
  let len = UArray.length !t1 in
  let t2 = ref (reroot p2) in
  if UArray.length !t2 <> len then invalid_arg "Parray.fold_left2";
  let rerooted_again1 = ref false in
  let check_rooted1 () = if not !rerooted_again1 && not (is_rooted p1)
    then (t1 := UArray.copy (reroot p1); rerooted_again1 := true)
  in
  let rerooted_again2 = ref false in
  let check_rooted2 () = if not !rerooted_again2 && not (is_rooted p2)
    then (t2 := UArray.copy (reroot p2); rerooted_again2 := true)
  in
  for i = 0 to len - 1 do
    check_rooted1 ();
    let v1 = UArray.unsafe_get !t1 i in
    check_rooted2 ();
    let v2 = UArray.unsafe_get !t2 i in
    r := f !r v1 v2
  done;
  f !r (default p1) (default p2)
