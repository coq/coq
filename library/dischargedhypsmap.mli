(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Libnames
open Term
open Environ
open Nametab
(*i*)

type discharged_hyps = section_path list

(*s Discharged hypothesis. Here we store the discharged hypothesis of each *)
(*  constant or inductive type declaration.                                *)

val set_discharged_hyps : section_path -> discharged_hyps -> unit
val get_discharged_hyps : section_path -> discharged_hyps
