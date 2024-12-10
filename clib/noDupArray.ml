(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


type 'a t = 'a option array * bool ref

let make n = Array.make n None, ref true

let test_validity b =
  if not !b then
  invalid_arg "Tried to reuse invalidated NoDupArray."

let invalidate b =
  test_validity b;
  b := false

let get i (a, b) =
  test_validity b;
  a.(i)

let is_filled i (a, b) =
  test_validity b;
  Option.has_some a.(i)

let add i e (a, b) =
  invalidate b;
  begin match a.(i) with
  | None -> a.(i) <- Some e
  | Some _ -> invalid_arg "Tried to add duplicate in NoDupArray."
  end;
  a, ref true

let fill_remaining e (a, b) =
  invalidate b;
  Array.iteri (fun i elt ->
    begin match elt with
    | None -> a.(i) <- Some e
    | Some _ -> ()
    end) a;
  a, ref true

let to_array (a, b) =
  invalidate b;
  Array.map (function Some e -> e | None -> invalid_arg "Tried to cast non-full NoDupArray.") a

let to_array_opt (a, b) =
  invalidate b;
  let exception Stop in
  try Some (Array.map (function Some e -> e | None -> raise Stop) a)
  with Stop -> None

module Internal = struct

  let unsafe_to_array (a, _) = a
end
