
(* $Id$ *)

open System
open Lib
open Summary

type state = Lib.frozen * Summary.frozen

let get_state () =
  (Lib.freeze(), freeze_summaries())

let set_state (fl,fs) =
  Lib.unfreeze fl;
  unfreeze_summaries fs

let state_magic_number = 19764

let (extern_state,intern_state) =
  let (raw_extern, raw_intern) = extern_intern state_magic_number ".coq" in
  (fun s -> raw_extern s (get_state())),
  (fun s -> set_state (raw_intern s))
