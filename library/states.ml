(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

let (extern_state,intern_state) =
  let (raw_extern, raw_intern) =
    extern_intern Coq_config.state_magic_number in
  (fun s ->
    raw_extern s (freeze ~marshallable:`Yes)),
  (fun s ->
    unfreeze (with_magic_number_check raw_intern s);
    Library.overwrite_library_filenames s)

(* Rollback. *)

let with_state_protection f x =
  let st = freeze ~marshallable:`No in
  try
    let a = f x in unfreeze st; a
  with reraise ->
    let reraise = Errors.push reraise in
    (unfreeze st; iraise reraise)

let with_state_protection_on_exception = Future.transactify
