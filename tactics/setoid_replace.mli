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
open Names

type morphism_signature = (bool option * constr_expr) list * constr_expr

val pr_morphism_signature : morphism_signature -> Pp.std_ppcmds

val register_replace : (constr -> constr -> tactic) -> unit
val register_general_rewrite : (bool -> constr -> tactic) -> unit

val print_setoids : unit -> unit

val equiv_list : unit -> constr list

val setoid_replace :
 constr option -> constr -> constr -> new_goals:constr list -> tactic
val setoid_replace_in :
 identifier -> constr option -> constr -> constr -> new_goals:constr list ->
  tactic

val general_s_rewrite : bool -> constr -> new_goals:constr list -> tactic
val general_s_rewrite_in :
 identifier -> bool -> constr -> new_goals:constr list -> tactic

val add_relation :
 constr_expr -> constr_expr -> constr_expr option -> constr_expr option -> unit

val add_setoid :
 Names.identifier -> constr_expr -> constr_expr -> constr_expr -> unit

val new_named_morphism :
 Names.identifier -> constr_expr -> morphism_signature option -> unit
