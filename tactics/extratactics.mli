(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Term
open Proof_type
open Rawterm

val h_discrHyp : identifier -> tactic
val h_injHyp : quantified_hypothesis -> tactic
val h_rewriteLR : constr -> tactic

val refine_tac : Genarg.open_constr -> tactic
