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
open Sign
open Environ
open Evd
open Refiner
open Proof_type
(*i*)

type wc = named_context sigma (* for a better reading of the following *)

(* Refinement of existential variables. *)

val rc_of_pfsigma : proof_tree sigma -> wc
val rc_of_glsigma : goal sigma -> wc

(* A [w_tactic] is a tactic which modifies the a set of evars of which
   a goal depend, either by instantiating one, or by declaring a new
   dependent goal *)
type w_tactic = wc -> wc

val startWalk : goal sigma -> wc * (wc -> tactic)

val extract_decl : evar -> w_tactic
val restore_decl : evar -> evar_info -> w_tactic
val w_Declare    : evar -> types -> w_tactic
val w_Define     : evar -> constr -> w_tactic

val w_Underlying : wc -> evar_map
val w_env        : wc -> env
val w_hyps       : wc -> named_context
val w_whd        : wc -> constr -> constr
val w_type_of    : wc -> constr -> constr
val w_add_sign   : (identifier * types) -> w_tactic

val w_whd_betadeltaiota : wc -> constr -> constr
val w_hnf_constr        : wc -> constr -> constr
val w_conv_x            : wc -> constr -> constr -> bool
val w_const_value       : wc -> constant -> constr
val w_defined_evar      : wc -> existential_key -> bool

val instantiate : int -> constr -> identifier Tacexpr.gsimple_clause -> tactic
(*
val instantiate_tac : tactic_arg list -> tactic
*)
val instantiate_pf_com : int -> Topconstr.constr_expr -> pftreestate -> pftreestate
