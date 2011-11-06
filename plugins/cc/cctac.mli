(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term
open Proof_type

val proof_tac: Ccproof.proof -> Proof_type.tactic

val cc_tactic : int -> constr list -> tactic

val cc_fail : tactic

val congruence_tac : int -> constr list -> tactic

val f_equal : tactic
