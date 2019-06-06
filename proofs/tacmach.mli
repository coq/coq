(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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
open Locus

(** Operations for handling terms under a local typing context. *)

open Evd

type tactic = Proofview.V82.tac

val sig_it  : 'a sigma   -> 'a
val project : Goal.goal sigma -> evar_map

val re_sig : 'a -> evar_map -> 'a sigma

val pf_concl              : Goal.goal sigma -> types
val pf_env                : Goal.goal sigma -> env
val pf_hyps               : Goal.goal sigma -> named_context
(*i val pf_untyped_hyps       : Goal.goal sigma -> (Id.t * constr) list i*)
val pf_hyps_types         : Goal.goal sigma -> (Id.t Context.binder_annot * types) list
val pf_nth_hyp_id         : Goal.goal sigma -> int -> Id.t
val pf_last_hyp           : Goal.goal sigma -> named_declaration
val pf_ids_of_hyps        : Goal.goal sigma -> Id.t list
val pf_unsafe_type_of     : Goal.goal sigma -> constr -> types
val pf_type_of            : Goal.goal sigma -> constr -> evar_map * types
val pf_hnf_type_of        : Goal.goal sigma -> constr -> types

val pf_get_hyp            : Goal.goal sigma -> Id.t -> named_declaration
val pf_get_hyp_typ        : Goal.goal sigma -> Id.t -> types

val pf_get_new_id         : Id.t -> Goal.goal sigma -> Id.t

val pf_apply : (env -> evar_map -> 'a) -> Goal.goal sigma -> 'a
val pf_eapply : (env -> evar_map -> 'a -> evar_map * 'b) -> 
  Goal.goal sigma -> 'a -> Goal.goal sigma * 'b
val pf_reduce :
  (env -> evar_map -> constr -> constr) ->
  Goal.goal sigma -> constr -> constr
val pf_e_reduce :
  (env -> evar_map -> constr -> evar_map * constr) ->
  Goal.goal sigma -> constr -> evar_map * constr

val pf_whd_all       : Goal.goal sigma -> constr -> constr
val pf_hnf_constr              : Goal.goal sigma -> constr -> constr
val pf_nf                      : Goal.goal sigma -> constr -> constr
val pf_nf_betaiota             : Goal.goal sigma -> constr -> constr
val pf_reduce_to_quantified_ind : Goal.goal sigma -> types -> (inductive * EInstance.t) * types
val pf_reduce_to_atomic_ind     : Goal.goal sigma -> types -> (inductive * EInstance.t) * types
val pf_compute                 : Goal.goal sigma -> constr -> constr
val pf_unfoldn    : (occurrences * evaluable_global_reference) list
  -> Goal.goal sigma -> constr -> constr

val pf_const_value : Goal.goal sigma -> pconstant -> constr
val pf_conv_x      : Goal.goal sigma -> constr -> constr -> bool

(** {6 Pretty-printing functions (debug only). } *)
val pr_gls    : Goal.goal sigma -> Pp.t

(** Variants of [Tacmach] functions built with the new proof engine *)
module New : sig

  val pf_apply : (env -> evar_map -> 'a) -> Proofview.Goal.t -> 'a

  (** FIXME: encapsulate the level in an existential type. *)
  val of_old : (Goal.goal Evd.sigma -> 'a) -> Proofview.Goal.t -> 'a

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

  val pf_compute : Proofview.Goal.t -> constr -> constr

  val pf_nf_evar : Proofview.Goal.t -> constr -> constr

end
