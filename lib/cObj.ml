(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
    let hash o = Hashtbl.hash (Obj.magic o : int)
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
  if not (in_table t) then begin
    if Obj.is_block t then begin
      add_in_table t;
      let n = Obj.size t in
      let tag = Obj.tag t in
      if tag < Obj.no_scan_tag then begin
        count := !count + 1 + n;
        for i = 0 to n - 1 do
          let f = Obj.field t i in traverse f
        done
      end else if tag = Obj.string_tag then
        count := !count + 1 + n
      else if tag = Obj.double_tag then
        count := !count + size_of_double
      else if tag = Obj.double_array_tag then
        count := !count + 1 + size_of_double * n
      else
        incr count
    end
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

(*s Total size of the allocated ocaml heap. *)

let heap_size () =
  let stat = Gc.stat ()
  and control = Gc.get () in
  let max_words_total = stat.Gc.heap_words + control.Gc.minor_heap_size in
  (max_words_total * (Sys.word_size / 8))

let heap_size_kb () = (heap_size () + 1023) / 1024
