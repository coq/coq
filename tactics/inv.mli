(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Genarg
open Tacexpr
open Rawterm
(*i*)

(* arnaud: trucs factices *)
type tactic = Tacticals.tactic
(* arnaud: /trucs factices *)

type inversion_status = Dep of constr option | NoDep

val inv_gen :
  bool -> inversion_kind -> inversion_status ->
    intro_pattern_expr -> quantified_hypothesis -> tactic
val invIn_gen :
  inversion_kind -> intro_pattern_expr -> identifier list -> 
    quantified_hypothesis -> tactic

val inv_clause :
  inversion_kind -> intro_pattern_expr -> identifier list ->
    quantified_hypothesis -> tactic

val inv : inversion_kind -> intro_pattern_expr ->
  quantified_hypothesis -> tactic

val dinv : inversion_kind -> constr option -> intro_pattern_expr ->
  quantified_hypothesis -> tactic

val half_inv_tac : identifier -> tactic
val inv_tac : identifier -> tactic
val inv_clear_tac : identifier -> tactic
val half_dinv_tac : identifier -> tactic
val dinv_tac : identifier -> tactic
val dinv_clear_tac : identifier -> tactic
