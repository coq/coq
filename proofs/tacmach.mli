(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

module Old :
sig

[@@@ocaml.warning "-3"]
type tactic = Proofview.V82.tac

val sig_it  : 'a sigma   -> 'a
val project : Evar.t sigma -> evar_map

val re_sig : 'a -> evar_map -> 'a sigma

val pf_concl              : Evar.t sigma -> types
val pf_env                : Evar.t sigma -> env
val pf_hyps               : Evar.t sigma -> named_context
(*i val pf_untyped_hyps       : Evar.t sigma -> (Id.t * constr) list i*)
val pf_hyps_types         : Evar.t sigma -> (Id.t Context.binder_annot * types) list
val pf_nth_hyp_id         : Evar.t sigma -> int -> Id.t
val pf_last_hyp           : Evar.t sigma -> named_declaration
val pf_ids_of_hyps        : Evar.t sigma -> Id.t list
val pf_type_of            : Evar.t sigma -> constr -> evar_map * types
val pf_hnf_type_of        : Evar.t sigma -> constr -> types
[@@ocaml.deprecated "This is a no-op now"]

val pf_get_hyp            : Evar.t sigma -> Id.t -> named_declaration
val pf_get_hyp_typ        : Evar.t sigma -> Id.t -> types

val pf_get_new_id         : Id.t -> Evar.t sigma -> Id.t

val pf_apply : (env -> evar_map -> 'a) -> Evar.t sigma -> 'a
val pf_eapply : (env -> evar_map -> 'a -> evar_map * 'b) ->
  Evar.t sigma -> 'a -> Evar.t sigma * 'b
val pf_reduce :
  (env -> evar_map -> constr -> constr) ->
  Evar.t sigma -> constr -> constr
[@@ocaml.deprecated "Use the version in Tacmach.New"]

val pf_e_reduce :
  (env -> evar_map -> constr -> evar_map * constr) ->
  Evar.t sigma -> constr -> evar_map * constr
[@@ocaml.deprecated "Use the version in Tacmach.New"]

val pf_whd_all       : Evar.t sigma -> constr -> constr
[@@ocaml.deprecated "Use the version in Tacmach.New"]
val pf_hnf_constr              : Evar.t sigma -> constr -> constr
[@@ocaml.deprecated "Use the version in Tacmach.New"]
val pf_nf                      : Evar.t sigma -> constr -> constr
[@@ocaml.deprecated "Use the version in Tacmach.New"]
val pf_nf_betaiota             : Evar.t sigma -> constr -> constr
val pf_reduce_to_quantified_ind : Evar.t sigma -> types -> (inductive * EInstance.t) * types
val pf_reduce_to_atomic_ind     : Evar.t sigma -> types -> (inductive * EInstance.t) * types
[@@ocaml.deprecated "Use Tacred.pf_reduce_to_atomic_ind"]
val pf_compute                 : Evar.t sigma -> constr -> constr
[@@ocaml.deprecated "Use the version in Tacmach.New"]
val pf_unfoldn    : (occurrences * Tacred.evaluable_global_reference) list
  -> Evar.t sigma -> constr -> constr
[@@ocaml.deprecated "Use Tacred.unfoldn"]

val pf_const_value : Evar.t sigma -> pconstant -> constr
[@@ocaml.deprecated "Use Environ.constant_value_in"]
val pf_conv_x      : Evar.t sigma -> constr -> constr -> bool
[@@ocaml.deprecated "Use the version in Tacmach.New"]

(** {6 Pretty-printing functions (debug only). } *)
val pr_gls    : Evar.t sigma -> Pp.t

[@@@ocaml.warning "+3"]
end
[@@ocaml.deprecated "Use the new engine"]

(** Variants of [Tacmach] functions built with the new proof engine *)

val pf_apply : (env -> evar_map -> 'a) -> Proofview.Goal.t -> 'a

val of_old : (Goal.goal Evd.sigma -> 'a) -> Proofview.Goal.t -> 'a
[@@ocaml.warning "-3"] [@@ocaml.deprecated "Use the new engine"]

val project : Proofview.Goal.t -> Evd.evar_map
val pf_env : Proofview.Goal.t -> Environ.env
val pf_concl : Proofview.Goal.t -> types

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

val pr_gls : Proofview.Goal.t -> Pp.t
