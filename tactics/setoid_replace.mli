(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term
open Proof_type
open Topconstr

val equiv_list : unit -> constr list

val setoid_replace : constr -> constr -> constr option -> tactic

val setoid_rewriteLR : constr -> tactic

val setoid_rewriteRL : constr -> tactic

val general_s_rewrite : bool -> constr -> tactic

val add_setoid : constr_expr -> constr_expr -> constr_expr -> unit

val new_named_morphism : Names.identifier -> constr_expr -> unit
