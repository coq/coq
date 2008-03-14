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

let freeze () =
  (Lib.freeze(), Summary.freeze_summaries())

let unfreeze (fl,fs) =
  Lib.unfreeze fl;
  Summary.unfreeze_summaries fs

let state_magic_number = 19764

let (extern_state,intern_state) =
  let (raw_extern, raw_intern) = extern_intern state_magic_number ".coq" in
  (fun s -> raw_extern s (freeze())),
  (fun s -> unfreeze (raw_intern (Library.get_load_paths ()) s))

(* Rollback. *)

let with_heavy_rollback f x =
  let st = freeze () in
  try 
    f x
  with reraise ->
    (unfreeze st; raise reraise)
