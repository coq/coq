(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


open Util

type 'a t = 'a option array * bool ref

let make n = Array.make n None, ref true

let test_validity b =
  if not !b then
    CErrors.anomaly Pp.(str "Tried to reuse invalidated NoDupArray.")

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
  | Some _ -> CErrors.anomaly Pp.(str "Tried to add duplicate in NoDupArray.")
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
  Array.map (function Some e -> e | None -> CErrors.anomaly Pp.(str "Tried to cast non-full NoDupArray.")) a

let to_array_opt (a, b) =
  invalidate b;
  let exception Stop in
  try Some (Array.map (function Some e -> e | None -> raise Stop) a)
  with Stop -> None

let pr pre (a, _) =
  Pp.(str"[|"++prvect_with_sep pr_semicolon (function None -> str "\u{2205}" (* Empty set *) | Some e -> pre e) a++str"|]")
