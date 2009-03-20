(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(* $Id$ *)

(* raises Not_found if no proof is found *)

type atom_env=
    {mutable next:int;
     mutable env:(Term.constr*int) list}

val make_form : atom_env ->
    Proof_type.goal Tacmach.sigma -> Term.types -> Proof_search.form

val make_hyps :
    atom_env ->
    Proof_type.goal Tacmach.sigma ->
    Term.types list ->
    (Names.identifier * Term.types option * Term.types) list ->
    (Names.identifier * Proof_search.form) list

val rtauto_tac : Proof_type.tactic
