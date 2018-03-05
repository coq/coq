(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(* raises Not_found if no proof is found *)


type atom_env=
    {mutable next:int;
     mutable env:(Constr.t*int) list}

val make_form : atom_env ->
    Goal.goal Evd.sigma -> EConstr.types -> Proof_search.form

val make_hyps :
    atom_env ->
    Goal.goal Evd.sigma ->
    EConstr.types list ->
    EConstr.named_context ->
    (Names.Id.t * Proof_search.form) list

val rtauto_tac : Tacmach.tactic
