(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Tacmach
(*i*)

type inversion_status = Dep of constr option | NoDep

val inv_gen :
  bool -> bool option -> inversion_status -> Rawterm.quantified_hypothesis -> tactic
val invIn_gen : bool option -> Rawterm.quantified_hypothesis -> identifier list -> tactic

val inv : bool option -> Rawterm.quantified_hypothesis -> tactic
val dinv : bool option -> constr option -> Rawterm.quantified_hypothesis -> tactic
val half_inv_tac : identifier -> tactic
val inv_tac : identifier -> tactic
val inv_clear_tac : identifier -> tactic
val half_dinv_tac : identifier -> tactic
val dinv_tac : identifier -> tactic
val dinv_clear_tac : identifier -> tactic
(*
val half_dinv_with : identifier -> constr -> tactic
val dinv_with : identifier -> constr -> tactic
val dinv_clear_with : identifier -> constr -> tactic
*)
(*
val invIn_tac : identifier -> identifier -> identifier list -> tactic
*)
