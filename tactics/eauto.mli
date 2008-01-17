(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Term
open Tacexpr
open Auto
open Topconstr
(*i*)

(* arnaud: trucs factices *)
type tactics = Tacticals.tactic
(* arnaud: /trucs factices *)

val rawwit_hintbases : hint_db_name list option raw_abstract_argument_type

val rawwit_auto_using : constr_expr list raw_abstract_argument_type

val e_assumption : tactic

val registered_e_assumption : tactic

val e_give_exact_constr : constr -> tactic

val gen_eauto : bool -> bool * int -> constr list -> 
  hint_db_name list option -> tactic
