(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Libnames

type discharged_hyps = full_path list

(** Discharged hypothesis. Here we store the discharged hypothesis of each
    constant or inductive type declaration. *)

val set_discharged_hyps : full_path -> discharged_hyps -> unit
val get_discharged_hyps : full_path -> discharged_hyps
