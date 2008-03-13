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

val start_new_single_proof : string -> 
                             Term.types -> 
                            (Term.constr -> Decl_kinds.proof_end -> unit) ->
                             unit

val start_a_new_proof_in_global_env : 
                              (Term.constr*string option) list -> 
                              (Term.constr list -> Decl_kinds.proof_end -> unit) -> 
                               unit


(*** Helper functions related to the Proof module ***)
