(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Quickfix management *)

type t = Loc.t * Pp.t
let make ~loc txt = loc, txt
let pp (_,x) = x
let pp_wloc (loc,x) =
  let open Pp in
  h (str "Replace " ++ Loc.pr loc ++ str " with " ++ x)
let loc (l,_) = l

let handle_stack = ref []

let register h = handle_stack := h::!handle_stack

let rec accumulate_qf acc stk e =
  match stk with
  | [] -> acc
  | h::stk -> accumulate_qf (h e :: acc) stk e

let from_exception e =
  try
    Ok (CList.flatten (accumulate_qf [] !handle_stack e))
  with exn ->
    let ei = Exninfo.capture exn in
    Error ei

let print e =
  let open Pp in
  match e with
  | [] -> mt ()
  | qf ->
    let open Pp in
    let qf = prlist_with_sep cut pp_wloc qf in
    v 0 (prlist_with_sep cut (fun x -> x) [str "Quickfix:"; qf])
