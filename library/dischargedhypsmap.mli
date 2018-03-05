(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Libnames

type discharged_hyps = full_path list

(** Discharged hypothesis. Here we store the discharged hypothesis of each
    constant or inductive type declaration. *)

val set_discharged_hyps : full_path -> discharged_hyps -> unit
val get_discharged_hyps : full_path -> discharged_hyps
