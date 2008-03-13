(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(***********************************************************************)
(*                                                                     *)
(*      This module proposes a number of methods to access             *)
(*      and use proofs (from module Proof) or the global proof         *)
(*      state (given by module Global_proof)                           *)
(*                                                                     *)
(***********************************************************************)

(*** Helper functions related to the Proof_global module ***)

let proof_starter_of_type_list typs =
  List.map (fun x -> (Global.env (), x, None)) typs

let start_new_single_proof name typ return =
  let return constrs pe =
    match constrs with
    | [c] -> return c pe
    | _ -> Util.anomaly "Proofutils.start_new_single_proof:
                         Proofs seems to have grown extra base goals."
  in
  Proof_global.start_a_new_proof (proof_starter_of_type_list [typ]) return

let start_a_new_proof_in_global_env typs_and_tags return =
  Proof_global.start_a_new_proof
    (List.map (fun (tp,tg) -> (Global.env (), tp, tg) ) typs_and_tags)
    return

(*** Helper functions related to the Proof module ***)
