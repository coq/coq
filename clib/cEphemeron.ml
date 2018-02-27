(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type key_type = int

type boxed_key = key_type ref ref

let mk_key : unit -> boxed_key =
  (* TODO: take a random value here. Is there a random function in OCaml? *) 
  let bid = ref 0 in
  (* According to OCaml Gc module documentation, Pervasives.ref is one of the
     few ways of getting a boxed value the compiler will never alias. *)
  fun () -> incr bid; Pervasives.ref (Pervasives.ref !bid)

(* A phantom type to preserve type safety *)
type 'a key = boxed_key

(* Comparing keys with == grants that if a key is unmarshalled (in the same
   process where it was created or in another one) it is not mistaken for
   an already existing one (unmarshal has no right to alias).  If the initial
   value of bid is taken at random, then one also avoids potential collisions *)
module HT = Hashtbl.Make(struct
  type t = key_type ref
  let equal k1 k2 = k1 == k2
  let hash id = !id
end)

(* A key is the (unique) value inside a boxed key, hence it does not
   keep its corresponding boxed key reachable (replacing key_type by boxed_key
   would make the key always reachable) *)
let values : Obj.t HT.t = HT.create 1001

(* To avoid a race condition between the finalization function and
   get/create on the values hashtable, the finalization function just
   enqueues in an imperative list the item to be collected.  Being the list
   imperative, even if the Gc enqueues an item while run_collection is operating,
   the tail of the list is eventually set to Empty on completion.
   Kudos to the authors of Why3 that came up with this solution for their
   implementation of weak hash tables! *)
type imperative_list = cell ref
and cell = Empty | Item of key_type ref * imperative_list

let collection_queue : imperative_list ref = ref (ref Empty)

let enqueue x = collection_queue := ref (Item (!x, !collection_queue))

let run_collection () =
  let rec aux l = match !l with
    | Empty -> ()
    | Item (k, tl) -> HT.remove values k; aux tl in
  let l = !collection_queue in
  aux l;
  l := Empty

(* The only reference to the boxed key is the one returned, when the user drops
   it the value eventually disappears from the values table above *)
let create (v : 'a) : 'a key =
  run_collection ();
  let k = mk_key () in
  HT.add values !k (Obj.repr v);
  Gc.finalise enqueue k;
  k

(* Avoid raising Not_found *)
exception InvalidKey
let get (k : 'a key) : 'a =
  run_collection ();
  try Obj.obj (HT.find values !k)
  with Not_found -> raise InvalidKey

(* Simple utils *)
let default k v =
  try get k
  with InvalidKey -> v

let iter_opt k f =
  match
    try Some (get k)
    with InvalidKey -> None
  with
  | None -> ()
  | Some v -> f v

let clear () = run_collection ()
