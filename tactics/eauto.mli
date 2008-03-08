(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Term
open Proof_type
open Tacexpr
open Auto
open Topconstr
(*i*)

val rawwit_hintbases : hint_db_name list option raw_abstract_argument_type

val rawwit_auto_using : constr_expr list raw_abstract_argument_type

val e_assumption : tactic

val registered_e_assumption : tactic

val e_resolve_constr :  constr -> tactic

val vernac_e_resolve_constr :  constr -> tactic

val e_give_exact_constr : constr -> tactic

val gen_eauto : bool -> bool * int -> constr list -> 
  hint_db_name list option -> tactic

val eauto_with_bases :
  bool ->
  bool * int ->
  Term.constr list -> Auto.Hint_db.t list -> Proof_type.tactic
