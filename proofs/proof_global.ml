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
(*      This module defines the global proof environment               *)
(*      Especially it keeps tracks of whether or not there is          *)
(*      a proof which is currently being edited.                       *)
(*                                                                     *)
(***********************************************************************)

(* arnaud: commenter ce module *)

let current_proof = ref None

let there_is_a_proof () = Option.has_some !current_proof

exception NoCurrentProof
let give_me_the_proof () = 
  match !current_proof with
  | None -> raise NoCurrentProof
  | Some p -> p

exception ProofInProgress
let start_a_new_proof l return =
  if there_is_a_proof () then
    raise ProofInProgress
  else
    current_proof := Some (Proof.start l return)

(* arnaud: possible de discarder quand il n'y a pas de preuve ?
   ou tracking pour debugging ? *)
let discard () = current_proof := None




(*** **)

(* arnaud: debbugging ? *)
let pr_subgoals pr_fun =
  match !current_proof with
  | None -> Pp.str ""
  | Some p -> Proof.pr_subgoals p pr_fun



let db_run_tactic_on env n tac =
  match !current_proof with
  | None -> ()
  | Some cur -> Proof.run_tactic env (Proofview.tclFOCUS n tac) cur
