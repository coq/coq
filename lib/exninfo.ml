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

module Store = Store.Make(struct end)

type 'a t = 'a Store.field

let token = Obj.repr "HACK"
(** Unique token used to recognize enriched exceptions. *)

let make = Store.field

(** Discriminate normal data w.r.t enriched exceptions *)
let is_data obj =
  Obj.is_block obj && Obj.size obj = 2 && Obj.field obj 0 == token

(** As [Array.blit] *)
let blit obj1 off1 obj2 off2 len =
  for i = 0 to len - 1 do
    let data = Obj.field obj1 (off1 + i) in
    Obj.set_field obj2 (off2 + i) data
  done

(** Retrieve the optional backtrace set in an exception. *)
let get (e : exn) i =
  let obj = Obj.repr e in
  let len = Obj.size obj in
  let lst = Obj.field obj (len - 1) in
  if is_data lst then
    let data = Obj.obj (Obj.field lst 1) in
    Store.get data i
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
    let data = Store.set data i v in
    let ans = Obj.dup obj in
    let data = Obj.repr (token, data) in
    let () = Obj.set_field ans (len - 1) data in
    Obj.obj ans
  else
    (** This was a plain exception *)
    let ans = Obj.new_block 0 (succ len) in
    (** We build the new enriched exception from scratch *)
    let () = blit obj 0 ans 0 len in
    let data = Store.set Store.empty i v in
    let data = Obj.repr (token, data) in
    let () = Obj.set_field ans len data in
    Obj.obj ans

let clear e =
  let obj = Obj.repr e in
  let len = Obj.size obj in
  let lst = Obj.field obj (len - 1) in
  if is_data lst then
    let ans = Obj.new_block 0 (pred len) in
    let () = blit obj 0 ans 0 (pred len) in
    Obj.obj ans
  else e

let copy (src : exn) (dst : exn) =
  let obj = Obj.repr src in
  let len = Obj.size obj in
  let lst = Obj.field obj (len - 1) in
  if is_data lst then
    (** First object has data *)
    let src_data = Obj.obj (Obj.field lst 1) in
    let obj = Obj.repr dst in
    let len = Obj.size obj in
    let lst = Obj.field obj (len - 1) in
    if is_data lst then
      (** second object has data *)
      let dst_data = Obj.obj (Obj.field lst 1) in
      let ans = Obj.dup obj in
      let data = Obj.repr (token, Store.merge src_data dst_data) in
      let () = Obj.set_field ans len data in
      Obj.obj ans
    else
      (** second object has no data *)
      let ans = Obj.new_block 0 (succ len) in
      (** We build the new enriched exception from scratch *)
      let () = blit obj 0 ans 0 len in
      let data = Obj.repr (token, src_data) in
      let () = Obj.set_field ans len data in
      Obj.obj ans
  else dst
