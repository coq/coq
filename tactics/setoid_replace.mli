(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Proof_type
open Genarg

val equiv_list : unit -> constr list

val setoid_replace : constr -> constr -> constr option -> tactic

val setoid_rewriteLR : constr -> tactic

val setoid_rewriteRL : constr -> tactic

val general_s_rewrite : bool -> constr -> tactic

val add_setoid : constr_ast -> constr_ast -> constr_ast -> unit

val new_named_morphism : Names.identifier -> constr_ast -> unit
