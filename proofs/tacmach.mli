(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open EConstr
open Proof_type
open Redexpr
open Locus

(** Operations for handling terms under a local typing context. *)

type 'a sigma   = 'a Evd.sigma
[@@ocaml.deprecated "alias of Evd.sigma"]

open Evd
type tactic     = Proof_type.tactic;;

val sig_it  : 'a sigma   -> 'a
val project : goal sigma -> evar_map

val re_sig : 'a -> evar_map -> 'a sigma

val unpackage : 'a sigma -> evar_map ref * 'a
[@@ocaml.deprecated "Do not use [evar_map ref]"]
val repackage : evar_map ref -> 'a -> 'a sigma
[@@ocaml.deprecated "Do not use [evar_map ref]"]
val apply_sig_tac :
  evar_map ref -> (goal sigma -> (goal list) sigma) -> goal -> (goal list)
[@@ocaml.deprecated "Do not use [evar_map ref]"]

val pf_concl              : goal sigma -> types
val pf_env                : goal sigma -> env
val pf_hyps               : goal sigma -> named_context
(*i val pf_untyped_hyps       : goal sigma -> (Id.t * constr) list i*)
val pf_hyps_types         : goal sigma -> (Id.t * types) list
val pf_nth_hyp_id         : goal sigma -> int -> Id.t
val pf_last_hyp           : goal sigma -> named_declaration
val pf_ids_of_hyps        : goal sigma -> Id.t list
val pf_global             : goal sigma -> Id.t -> constr
val pf_unsafe_type_of            : goal sigma -> constr -> types
val pf_type_of            : goal sigma -> constr -> evar_map * types
val pf_hnf_type_of        : goal sigma -> constr -> types

val pf_get_hyp            : goal sigma -> Id.t -> named_declaration
val pf_get_hyp_typ        : goal sigma -> Id.t -> types

val pf_get_new_id  : Id.t      -> goal sigma -> Id.t

val pf_reduction_of_red_expr : goal sigma -> red_expr -> constr -> evar_map * constr


val pf_apply : (env -> evar_map -> 'a) -> goal sigma -> 'a
val pf_eapply : (env -> evar_map -> 'a -> evar_map * 'b) -> 
  goal sigma -> 'a -> goal sigma * 'b
val pf_reduce :
  (env -> evar_map -> constr -> constr) ->
  goal sigma -> constr -> constr
val pf_e_reduce :
  (env -> evar_map -> constr -> evar_map * constr) ->
  goal sigma -> constr -> evar_map * constr

val pf_whd_all       : goal sigma -> constr -> constr
val pf_hnf_constr              : goal sigma -> constr -> constr
val pf_nf                      : goal sigma -> constr -> constr
val pf_nf_betaiota             : goal sigma -> constr -> constr
val pf_reduce_to_quantified_ind : goal sigma -> types -> (inductive * EInstance.t) * types
val pf_reduce_to_atomic_ind     : goal sigma -> types -> (inductive * EInstance.t) * types
val pf_compute                 : goal sigma -> constr -> constr
val pf_unfoldn    : (occurrences * evaluable_global_reference) list
  -> goal sigma -> constr -> constr

val pf_const_value : goal sigma -> pconstant -> constr
val pf_conv_x      : goal sigma -> constr -> constr -> bool
val pf_conv_x_leq  : goal sigma -> constr -> constr -> bool

(** {6 The most primitive tactics. } *)

val refiner                   : rule -> tactic
val refine_no_check           : constr -> tactic

(** {6 The most primitive tactics with consistency and type checking } *)

val refine           : constr -> tactic

(** {6 Pretty-printing functions (debug only). } *)
val pr_gls    : goal sigma -> Pp.t
val pr_glls   : goal list sigma -> Pp.t

(* Variants of [Tacmach] functions built with the new proof engine *)
module New : sig
  val pf_apply : (env -> evar_map -> 'a) -> Proofview.Goal.t -> 'a
  val pf_global : Id.t -> Proofview.Goal.t -> GlobRef.t
  (** FIXME: encapsulate the level in an existential type. *)
  val of_old : (Proof_type.goal Evd.sigma -> 'a) -> Proofview.Goal.t -> 'a

  val project : Proofview.Goal.t -> Evd.evar_map
  val pf_env : Proofview.Goal.t -> Environ.env
  val pf_concl : Proofview.Goal.t -> types

  (** WRONG: To be avoided at all costs, it typechecks the term entirely but
     forgets the universe constraints necessary to retypecheck it *)
  val pf_unsafe_type_of : Proofview.Goal.t -> constr -> types

  (** This function does no type inference and expects an already well-typed term.
      It recomputes its type in the fastest way possible (no conversion is ever involved) *)
  val pf_get_type_of : Proofview.Goal.t -> constr -> types

  (** This function entirely type-checks the term and computes its type
      and the implied universe constraints. *)
  val pf_type_of : Proofview.Goal.t -> constr -> evar_map * types
  val pf_conv_x : Proofview.Goal.t -> t -> t -> bool

  val pf_get_new_id  : Id.t -> Proofview.Goal.t -> Id.t
  val pf_ids_of_hyps : Proofview.Goal.t -> Id.t list
  val pf_ids_set_of_hyps : Proofview.Goal.t -> Id.Set.t
  val pf_hyps_types : Proofview.Goal.t -> (Id.t * types) list

  val pf_get_hyp : Id.t -> Proofview.Goal.t -> named_declaration
  val pf_get_hyp_typ        : Id.t -> Proofview.Goal.t -> types
  val pf_last_hyp           : Proofview.Goal.t -> named_declaration

  val pf_nf_concl : Proofview.Goal.t -> types
  val pf_reduce_to_quantified_ind : Proofview.Goal.t -> types -> (inductive * EInstance.t) * types

  val pf_hnf_constr : Proofview.Goal.t -> constr -> types
  val pf_hnf_type_of : Proofview.Goal.t -> constr -> types

  val pf_whd_all : Proofview.Goal.t -> constr -> constr
  val pf_compute : Proofview.Goal.t -> constr -> constr

  val pf_nf_evar : Proofview.Goal.t -> constr -> constr

end
