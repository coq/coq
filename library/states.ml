(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open System

type state = Lib.frozen * Summary.frozen

let get_state () =
  (Lib.freeze(), Summary.freeze_summaries())

let set_state (fl,fs) =
  Lib.unfreeze fl;
  Summary.unfreeze_summaries fs

let state_magic_number = 19764

let (extern_state,intern_state) =
  let (raw_extern, raw_intern) = extern_intern state_magic_number ".coq" in
  (fun s -> raw_extern s (get_state())),
  (fun s -> set_state (raw_intern (Library.get_load_path ()) s))

(* Rollback. *)

let freeze = get_state
let unfreeze = set_state

let with_heavy_rollback f x =
  let st = get_state () in
  try 
    f x
  with reraise ->
    (set_state st; raise reraise)
