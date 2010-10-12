(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Libnames
open Names
open Term
open Reduction
open Declarations
open Environ
open Inductive
open Libobject
open Lib
open Nametab

type discharged_hyps = full_path list

let discharged_hyps_map = ref Spmap.empty

let set_discharged_hyps sp hyps =
  discharged_hyps_map := Spmap.add sp hyps !discharged_hyps_map

let get_discharged_hyps sp =
  try
   Spmap.find sp !discharged_hyps_map
  with Not_found ->
    []

(*s Registration as global tables and rollback. *)

let init () =
  discharged_hyps_map := Spmap.empty

let freeze () = !discharged_hyps_map

let unfreeze dhm = discharged_hyps_map := dhm

let _ =
  Summary.declare_summary "discharged_hypothesis"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }
