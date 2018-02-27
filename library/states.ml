(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open System

type state = Lib.frozen * Summary.frozen

let summary_of_state = snd
let replace_summary (lib,_) s = lib, s

let freeze ~marshallable =
  (Lib.freeze ~marshallable, Summary.freeze_summaries ~marshallable)

let unfreeze (fl,fs) =
  Lib.unfreeze fl;
  Summary.unfreeze_summaries fs

let extern_state s =
  System.extern_state Coq_config.state_magic_number s (freeze ~marshallable:`Yes)

let intern_state s =
  unfreeze (with_magic_number_check (System.intern_state Coq_config.state_magic_number) s);
  Library.overwrite_library_filenames s

(* Rollback. *)

let with_state_protection f x =
  let st = freeze ~marshallable:`No in
  try
    let a = f x in unfreeze st; a
  with reraise ->
    let reraise = CErrors.push reraise in
    (unfreeze st; iraise reraise)
