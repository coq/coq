(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type state = Lib.frozen * Summary.frozen

let lib_of_state = fst
let summary_of_state = snd
let replace_summary (lib,_) st = lib, st
let replace_lib (_,st) lib = lib, st

let freeze ~marshallable =
  (Lib.freeze (), Summary.freeze_summaries ~marshallable)

let unfreeze (fl,fs) =
  Lib.unfreeze fl;
  Summary.unfreeze_summaries fs

(* Rollback. *)

let with_state_protection f x =
  let st = freeze ~marshallable:false in
  try
    let a = f x in unfreeze st; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    (unfreeze st; Exninfo.iraise reraise)
