(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Logical and physical size of ocaml values. *)

(** {6 Logical sizes} *)

let c = ref 0
let s = ref 0
let b = ref 0
let m = ref 0

let rec obj_stats d t =
  if Obj.is_int t then m := max d !m
  else if Obj.tag t >= Obj.no_scan_tag then
    if Obj.tag t = Obj.string_tag then
      (c := !c + Obj.size t; b := !b + 1; m := max d !m)
    else if Obj.tag t = Obj.double_tag then
      (s := !s + 2; b := !b + 1; m := max d !m)
    else if Obj.tag t = Obj.double_array_tag then
      (s := !s + 2 * Obj.size t; b := !b + 1; m := max d !m)
    else (b := !b + 1; m := max d !m)
  else
    let n = Obj.size t in
    s := !s + n; b := !b + 1;
    block_stats (d + 1) (n - 1) t

and block_stats d i t =
  if i >= 0 then (obj_stats d (Obj.field t i); block_stats d (i-1) t)

let obj_stats a =
  c := 0; s:= 0; b:= 0; m:= 0;
  obj_stats 0 (Obj.repr a);
  (!c, !s + !b, !m)

(** {6 Physical sizes} *)

(*s Pointers already visited are stored in a hash-table, where
    comparisons are done using physical equality. *)

module H = Hashtbl.Make(
  struct
    type t = Obj.t
    let equal = (==)
    let hash = Hashtbl.hash
  end)

let node_table = (H.create 257 : unit H.t)

let in_table o = try H.find node_table o; true with Not_found -> false

let add_in_table o = H.add node_table o ()

let reset_table () = H.clear node_table

(*s Objects are traversed recursively, as soon as their tags are less than
    [no_scan_tag]. [count] records the numbers of words already visited. *)

let size_of_double = Obj.size (Obj.repr 1.0)

let count = ref 0

let rec traverse t =
  if not (in_table t) && Obj.is_block t then begin
    add_in_table t;
    let n = Obj.size t in
    let tag = Obj.tag t in
    if tag < Obj.no_scan_tag then
      begin
        count := !count + 1 + n;
        for i = 0 to n - 1 do traverse (Obj.field t i) done
      end
    else if tag = Obj.string_tag then
      count := !count + 1 + n
    else if tag = Obj.double_tag then
      count := !count + size_of_double
    else if tag = Obj.double_array_tag then
      count := !count + 1 + size_of_double * n
    else
      incr count
  end

(*s Sizes of objects in words and in bytes. The size in bytes is computed
    system-independently according to [Sys.word_size]. *)

let size o =
  reset_table ();
  count := 0;
  traverse (Obj.repr o);
  !count

let size_b o = (size o) * (Sys.word_size / 8)

let size_kb o = (size o) / (8192 / Sys.word_size)

(** {6 Physical sizes with sharing} *)

(** This time, all the size of objects are computed with respect
    to a larger object containing them all, and we only count
    the new blocks not already seen earlier in the left-to-right
    visit of the englobing object.

    The very same object could have a zero size or not, depending
    of the occurrence we're considering in the englobing object.
    For speaking of occurrences, we use an [int list] for a path
    of field indexes from the outmost block to the one we're looking.
    In the list, the leftmost integer is the field index in the deepest
    block.
*)

(** We now store in the hashtable the size (with sharing), and
    also the position of the first occurrence of the object *)

let node_sizes = (H.create 257 : (int*int list) H.t)
let get_size o = H.find node_sizes o
let add_size o n pos = H.replace node_sizes o (n,pos)
let reset_sizes () = H.clear node_sizes
let global_object = ref (Obj.repr 0)

(** [sum n f] is [f 0 + f 1 + ... + f (n-1)], evaluated from left to right *)

let sum n f =
  let rec loop k acc = if k >= n then acc else loop (k+1) (acc + f k)
  in loop 0 0

(** Recursive visit of the main object, filling the hashtable *)

let rec compute_size o pos =
  if not (Obj.is_block o) then 0
  else
    try
      let _ = get_size o in 0 (* already seen *)
    with Not_found ->
      let n = Obj.size o in
      add_size o (-1) pos (* temp size, for cyclic values *);
      let tag = Obj.tag o in
      let size =
        if tag < Obj.no_scan_tag then
          1 + n + sum n (fun i -> compute_size (Obj.field o i) (i::pos))
        else if tag = Obj.string_tag then
          1 + n
        else if tag = Obj.double_tag then
          size_of_double
        else if tag = Obj.double_array_tag then
          size_of_double * n
        else
          1
      in
      add_size o size pos;
      size

(** Provides the global object in which we'll search shared sizes *)

let register_shared_size t =
  let o = Obj.repr t in
  reset_sizes ();
  global_object := o;
  ignore (compute_size o [])

(** Shared size of an object with respect to the global object given
    by the last [register_shared_size] *)

let shared_size pos o =
  if not (Obj.is_block o) then 0
  else
    let size,pos' =
      try get_size o
      with Not_found -> failwith "shared_size: unregistered structure ?"
    in
    match pos with
      | Some p when p <> pos' -> 0
      | _ -> size

let shared_size_of_obj t = shared_size None (Obj.repr t)

(** Shared size of the object at some positiion in the global object given
    by the last [register_shared_size] *)

let shared_size_of_pos pos =
  let rec obj_of_pos o = function
    | [] -> o
    | n::pos' ->
      let o' = obj_of_pos o pos' in
      assert (Obj.is_block o' && n < Obj.size o');
      Obj.field o' n
  in
  shared_size (Some pos) (obj_of_pos !global_object pos)


(*s Total size of the allocated ocaml heap. *)

let heap_size () =
  let stat = Gc.stat ()
  and control = Gc.get () in
  let max_words_total = stat.Gc.heap_words + control.Gc.minor_heap_size in
  (max_words_total * (Sys.word_size / 8))

let heap_size_kb () = (heap_size () + 1023) / 1024
