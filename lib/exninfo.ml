(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** Enriched exceptions have an additional field at the end of their usual data
    containing a pair composed of the distinguishing [token] and the backtrace
    information. We discriminate the token by pointer equality. *)

type 'a t = int
(** Information is retrieved through this identifier. *)

let token = Obj.repr "HACK"
(** Unique token used to recognize enriched exceptions. *)

let make =
  let cnt = ref 0 in fun () ->
    let ans = !cnt in
    let () = incr cnt in
    ans

let rec assoc_aux (i : int) = function
| [] -> raise Exit
| (j, v) :: l ->
  if i = j then v else assoc_aux i l

let assoc i l =
  try Some (assoc_aux i l) with Exit -> None

let rec add_assoc (i : int) v = function
| [] -> [i, v]
| (j, w) :: l ->
  if i = j then (j, v) :: l
  else (j, w) :: add_assoc i v l

(** Discriminate normal data w.r.t enriched exceptions *)
let is_data obj =
  Obj.is_block obj && Obj.size obj = 2 && Obj.field obj 0 == token

(** Retrieve the optional backtrace set in an exception. *)
let get (e : exn) i =
  let obj = Obj.repr e in
  let len = Obj.size obj in
  let lst = Obj.field obj (len - 1) in
  if is_data lst then
    let data = Obj.obj (Obj.field lst 1) in
    assoc i data
  else None

(** Add data to any exception *)
let add e i v : exn =
  let obj = Obj.repr e in
  let len = Obj.size obj in
  let lst = Obj.field obj (len - 1) in
  if is_data lst then
    (** The exception was already enriched *)
    let data = Obj.obj (Obj.field lst 1) in
    (** We retrieve the old information and update it *)
    let data = add_assoc i v data in
    let ans = Obj.dup obj in
    let data = Obj.repr (token, data) in
    let () = Obj.set_field ans (len - 1) data in
    Obj.obj ans
  else
    (** This was a plain exception *)
    let ans = Obj.new_block 0 (succ len) in
    (** We build the new enriched exception from scratch *)
    let () =
      for i = 0 to len - 1 do
        Obj.set_field ans i (Obj.field obj i)
      done
    in
    let data = Obj.repr (token, [i, v]) in
    let () = Obj.set_field ans len data in
    Obj.obj ans
