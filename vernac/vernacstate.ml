(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = {
  system  : States.state;        (* summary + libstack *)
  proof   : Proof_global.t;      (* proof state *)
  shallow : bool                 (* is the state trimmed down (libstack) *)
}

let s_cache = ref None
let s_proof = ref None

let invalidate_cache () =
  s_cache := None;
  s_proof := None

let update_cache rf v =
  rf := Some v; v

let do_if_not_cached rf f v =
  match !rf with
  | None ->
    rf := Some v; f v
  | Some vc when vc != v ->
    rf := Some v; f v
  | Some _ ->
    ()

let freeze_interp_state marshallable =
  { system = update_cache s_cache (States.freeze ~marshallable);
    proof  = update_cache s_proof (Proof_global.freeze ~marshallable);
    shallow = marshallable = `Shallow }

let unfreeze_interp_state { system; proof } =
  do_if_not_cached s_cache States.unfreeze system;
  do_if_not_cached s_proof Proof_global.unfreeze proof
