(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* we could want to generalize such that some constructors of a sum type are ignored
   (eg to skip constr leaves)
   something like [Sum of type_descr array maybe_remember array]
   with [type 'a maybe_remember = Ignore | Remember of 'a | PassThrough of 'a].
   Not sure if useful enough to bother.
*)

type type_descr =
  | Ignore
  | Remember of type_descr
  | Array of type_descr
  | Sum of type_descr array array
  | Proxy of { mutable proxy : type_descr }

let remember x =
  let () = match x with
    | Remember _ -> assert false
    | _ -> ()
  in
  Remember x

let ignore = Ignore

let array x = Array x

let sum = function
  | [||] -> assert false
  | x ->
  assert (Array.for_all (function [||] -> false | _ -> true) x);
  Sum x

let tuple x = sum [|x|]

let pair a b = tuple [|a;b|]

let rec productive = function
  | Ignore | Array _ | Sum _ -> true
  | Remember x -> productive x
  | Proxy _ -> false

let cofix f =
  let p = Proxy { proxy = Ignore } in
  let v = f p in
  assert (productive v);
  let () = match p with
    | Proxy p -> p.proxy <- v;
    | _ -> assert false
  in
  v

let list x = cofix (fun x_list -> sum [|[|x;x_list|]|])

let slist x = cofix (fun x_slist -> sum [|[|x;x_slist|];[|ignore;x_slist|]|])

type sharing_info =
  | Fresh of int
  | Seen of int

(* format: stream of encoded ints such that
   0 means a new object
   otherwise [n] means a reference to [n - 1] (absolute)

   int encoding: one or several bytes like 1xxxxxxx 1yyyyyyy 0zzzzzzz.
   First bytes have top bit 1, last byte has top bit 0.
   Each byte carries 7 bits of the number.
   Bytes come in big-endian order: xxxxxxx are the 7 high-order bits,
   zzzzzzzz the 7 low-order bits.
*)
external analyse_core : type_descr -> Obj.t -> string = "coq_rec_analyse"

(* XXX it seems in practice sequences of fresh nodes are common, so we get a bunch of 0s
   maybe it would be better to change the format to a sequence of
   "the next $n are fresh" and "non fresh id $n"
   instead of the current "1 fresh" and "non fresh id $n".
*)

type analysis = {
  data : string;
  offset : int;
  seen : int;
}

let analysis_equal x y =
  (* no need to check [seen] *)
  (x.data == y.data || String.equal x.data y.data)
  && Int.equal x.offset y.offset

let analyse descr v =
  let s = analyse_core descr v in
  { data = s; offset = 0; seen = -1; }

let raw_length {data} = String.length data

let read_int data offset : int * int =
  let rec aux acc offset =
    let i = Char.code (String.get data offset) in
    if i < 0x80 then (acc lsl 7) + i, offset + 1
    else aux ((acc lsl 7) + (i land 0x7f)) (offset+1)
  in
  aux 0 offset

let step {data; offset; seen;} =
  let this, offset = read_int data offset in
  let info, seen = if this = 0 then Fresh (seen+1), seen+1
    else Seen (this - 1), seen
  in
  {data; offset; seen}, info

let is_done { data; offset } = String.length data = offset

let max_index {data; offset; seen} =
  let rec loop data offset seen =
    if String.length data = offset then seen
    else
      let this, offset = read_int data offset in
      let seen = if this = 0 then seen+1 else seen in
      loop data offset seen
  in
  loop data offset seen

let rec to_list_rev acc x =
  if x.offset = String.length x.data then acc
  else
    let x, info = step x in
    to_list_rev (info::acc) x

let to_list x = List.rev (to_list_rev [] x)

let raw x = x.data
