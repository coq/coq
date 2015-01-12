(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
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
    (Names.Id.t * Term.types option * Term.types) list ->
    (Names.Id.t * Proof_search.form) list

val rtauto_tac : Proof_type.tactic
