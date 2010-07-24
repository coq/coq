(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open System

type state = Lib.frozen * Summary.frozen

let freeze () =
  (Lib.freeze(), Summary.freeze_summaries())

let unfreeze (fl,fs) =
  Lib.unfreeze fl;
  Summary.unfreeze_summaries fs

let (extern_state,intern_state) =
  let (raw_extern, raw_intern) =
    extern_intern Coq_config.state_magic_number ".coq" in
  (fun s -> raw_extern s (freeze())),
  (fun s ->
    unfreeze
      (with_magic_number_check (raw_intern (Library.get_load_paths ())) s);
    Library.overwrite_library_filenames s)

(* Rollback. *)

let with_heavy_rollback f x =
  let st = freeze () in
  try
    f x
  with reraise ->
    (unfreeze st; raise reraise)

let with_state_protection f x =
  let st = freeze () in
  try
    let a = f x in unfreeze st; a
  with reraise ->
    (unfreeze st; raise reraise)
