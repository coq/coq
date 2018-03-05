(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Adapted from Damien Doligez, projet Para, INRIA Rocquencourt,
    OCaml stdlib. *)

(** The following functor is a specialized version of [Weak.Make].
    Here, the responsibility of computing the hash function is now
    given to the caller, which makes possible the interleaving of the
    hash key computation and the hash-consing. *)

module type EqType = sig
  type t
  val eq : t -> t -> bool
end

type statistics = {
  num_bindings: int;
  num_buckets: int;
  max_bucket_length: int;
  bucket_histogram: int array
}

module type S = sig
  type elt
  type t
  val create : int -> t
  val clear : t -> unit
  val repr : int -> elt -> t -> elt
  val stats : t -> statistics
end

module Make (E : EqType) =
  struct

  type elt = E.t

  let emptybucket = Weak.create 0

  type t = {
    mutable table : elt Weak.t array;
    mutable hashes : int array array;
    mutable limit : int;               (* bucket size limit *)
    mutable oversize : int;            (* number of oversize buckets *)
    mutable rover : int;               (* for internal bookkeeping *)
  }

  let get_index t h = (h land max_int) mod (Array.length t.table)

  let limit = 7
  let over_limit = 2

  let create sz =
    let sz = if sz < 7 then 7 else sz in
    let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
    {
      table = Array.make sz emptybucket;
      hashes = Array.make sz [| |];
      limit = limit;
      oversize = 0;
      rover = 0;
    }

  let clear t =
    for i = 0 to Array.length t.table - 1 do
      t.table.(i) <- emptybucket;
      t.hashes.(i) <- [| |];
    done;
    t.limit <- limit;
    t.oversize <- 0

  let iter_weak f t =
    let rec iter_bucket i j b =
      if i >= Weak.length b then () else
      match Weak.check b i with
      | true -> f b t.hashes.(j) i; iter_bucket (i+1) j b
      | false -> iter_bucket (i+1) j b
    in
    for i = 0 to pred (Array.length t.table) do
      iter_bucket 0 i (Array.unsafe_get t.table i)
    done

  let rec count_bucket i b accu =
    if i >= Weak.length b then accu else
    count_bucket (i+1) b (accu + (if Weak.check b i then 1 else 0))

  let min x y = if x - y < 0 then x else y

  let next_sz n = min (3 * n / 2 + 3) Sys.max_array_length
  let prev_sz n = ((n - 3) * 2 + 2) / 3

  let test_shrink_bucket t =
    let bucket = t.table.(t.rover) in
    let hbucket = t.hashes.(t.rover) in
    let len = Weak.length bucket in
    let prev_len = prev_sz len in
    let live = count_bucket 0 bucket 0 in
    if live <= prev_len then begin
      let rec loop i j =
        if j >= prev_len then begin
          if Weak.check bucket i then loop (i + 1) j
          else if Weak.check bucket j then begin
            Weak.blit bucket j bucket i 1;
            hbucket.(i) <- hbucket.(j);
            loop (i + 1) (j - 1);
          end else loop i (j - 1);
        end;
      in
      loop 0 (Weak.length bucket - 1);
      if prev_len = 0 then begin
        t.table.(t.rover) <- emptybucket;
        t.hashes.(t.rover) <- [| |];
      end else begin
        Obj.truncate (Obj.repr bucket) (prev_len + 1);
        Obj.truncate (Obj.repr hbucket) prev_len;
      end;
      if len > t.limit && prev_len <= t.limit then t.oversize <- t.oversize - 1;
    end;
    t.rover <- (t.rover + 1) mod (Array.length t.table)

  let rec resize t =
    let oldlen = Array.length t.table in
    let newlen = next_sz oldlen in
    if newlen > oldlen then begin
      let newt = create newlen in
      let add_weak ob oh oi =
        let setter nb ni _ = Weak.blit ob oi nb ni 1 in
        let h = oh.(oi) in
        add_aux newt setter None h (get_index newt h);
      in
      iter_weak add_weak t;
      t.table <- newt.table;
      t.hashes <- newt.hashes;
      t.limit <- newt.limit;
      t.oversize <- newt.oversize;
      t.rover <- t.rover mod Array.length newt.table;
    end else begin
      t.limit <- max_int;             (* maximum size already reached *)
      t.oversize <- 0;
    end

  and add_aux t setter d h index =
    let bucket = t.table.(index) in
    let hashes = t.hashes.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then begin
        let newsz = min (3 * sz / 2 + 3) (Sys.max_array_length - 1) in
        if newsz <= sz then failwith "Weak.Make: hash bucket cannot grow more";
        let newbucket = Weak.create newsz in
        let newhashes = Array.make newsz 0 in
        Weak.blit bucket 0 newbucket 0 sz;
        Array.blit hashes 0 newhashes 0 sz;
        setter newbucket sz d;
        newhashes.(sz) <- h;
        t.table.(index) <- newbucket;
        t.hashes.(index) <- newhashes;
        if sz <= t.limit && newsz > t.limit then begin
          t.oversize <- t.oversize + 1;
          for _i = 0 to over_limit do test_shrink_bucket t done;
        end;
        if t.oversize > Array.length t.table / over_limit then resize t
      end else if Weak.check bucket i then begin
        loop (i + 1)
      end else begin
        setter bucket i d;
        hashes.(i) <- h
      end
    in
    loop 0

  let find_or h t d ifnotfound =
    let index = get_index t h in
    let bucket = t.table.(index) in
    let hashes = t.hashes.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then ifnotfound index
      else if Int.equal h hashes.(i) then begin
        match Weak.get bucket i with
        | Some v when E.eq v d -> v
        | _ -> loop (i + 1)
      end else loop (i + 1)
    in
    loop 0

  let repr h d t =
    let ifnotfound index = add_aux t Weak.set (Some d) h index; d in
    find_or h t d ifnotfound

  let stats t =
    let fold accu bucket = max (count_bucket 0 bucket 0) accu in
    let max_length = Array.fold_left fold 0 t.table in
    let histogram = Array.make (max_length + 1) 0 in
    let iter bucket =
      let len = count_bucket 0 bucket 0 in
      histogram.(len) <- succ histogram.(len)
    in
    let () = Array.iter iter t.table in
    let fold (num, len, i) k = (num + k * i, len + k, succ i) in
    let (num, len, _) = Array.fold_left fold (0, 0, 0) histogram in
    {
      num_bindings = num;
      num_buckets = len;
      max_bucket_length = Array.length histogram;
      bucket_histogram = histogram;
    }

end

module Combine = struct
    (* These are helper functions to combine the hash keys in a similar
       way as [Hashtbl.hash] does. The constants [alpha] and [beta] must
       be prime numbers. There were chosen empirically. Notice that the
       problem of hashing trees is hard and there are plenty of study on
       this topic. Therefore, there must be room for improvement here. *)
    let alpha = 65599
    let beta  = 7
    let combine x y     = x * alpha + y
    let combine3 x y z   = combine x (combine y z)
    let combine4 x y z t = combine x (combine3 y z t)
    let combine5 x y z t u = combine x (combine4 y z t u)
    let combinesmall x y = beta * x + y
end
