(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


type 'a t = 'a option array option ref

let return a : 'a t = ref (Some a)

let if_valid (r : 'a t) =
  match !r with
  | Some a -> a
  | None -> invalid_arg "Tried to reuse invalidated NoDupArray."

(** Non-destructive get operator *)
let (let+) r f =
  f (if_valid r)

let destruct_get r =
  let+ a = r in
  r := None;
  a

(** Destructive get operator *)
let (let-) r f =
  f (destruct_get r)

let update r f : 'b t =
  let- a = r in
  return (f a)

(** Updating functor operator *)
let (let*) = update


let make n = return (Array.make n None)

let get i a =
  let+ a = a in
  a.(i)

let is_filled i a =
  let+ a = a in
  Option.has_some a.(i)

let add i e a =
  let* a = a in
  begin match a.(i) with
  | None -> a.(i) <- Some e
  | Some _ -> invalid_arg "Tried to add duplicate in NoDupArray."
  end;
  a

let fill_remaining e a =
  let* a = a in
  Array.iteri (fun i elt ->
    begin match elt with
    | None -> a.(i) <- Some e
    | Some _ -> ()
    end) a;
  a

let to_array a =
  let- a = a in
  Array.map (function Some e -> e | None -> invalid_arg "Tried to cast non-full NoDupArray.") a

let to_array_opt a =
  let- a = a in
  let exception Stop in
  try Some (Array.map (function Some e -> e | None -> raise Stop) a)
  with Stop -> None

module Internal = struct

  let unsafe_to_array = if_valid
end
