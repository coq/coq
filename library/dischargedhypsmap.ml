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

let discharged_hyps_map = Summary.ref Spmap.empty ~name:"discharged_hypothesis"

let set_discharged_hyps sp hyps =
  discharged_hyps_map := Spmap.add sp hyps !discharged_hyps_map

let get_discharged_hyps sp =
  try Spmap.find sp !discharged_hyps_map with Not_found -> []
