
(* $Id$ *)

open System
open Lib
open Summary

type state = Lib.frozen * Summary.frozen

let get_state () =
  (Lib.freeze(), freeze_summaries())

let set_state (fl,fs) =
  Lib.unfreeze fl;
  unfreeze_summaries fs;
  Lib.declare_initial_state()

let state_magic_number = 19764

let (extern_state,intern_state) =
  let (raw_extern, raw_intern) = extern_intern state_magic_number ".coq" in
  (fun s -> raw_extern s (get_state())),
  (fun s -> set_state (raw_intern s))

(* Rollback. *)

let freeze = get_state
let unfreeze = set_state

let with_heavy_rollback f x =
  let sum = freeze_summaries ()
  and flib = freeze() in
  try 
    f x
  with reraise -> begin
    unfreeze_summaries sum;
    unfreeze flib;
    raise reraise
  end
