(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ
open EConstr

(** Operations for handling terms under a local typing context. *)

open Evd

(** Variants of [Tacmach] functions built with the new proof engine *)

val pf_apply : (env -> evar_map -> 'a) -> Proofview.Goal.t -> 'a

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

val pf_hnf_constr : Proofview.Goal.t -> constr -> types
val pf_hnf_type_of : Proofview.Goal.t -> constr -> types

val pf_compute : Proofview.Goal.t -> constr -> constr
val pf_whd_compute : Proofview.Goal.t -> constr -> constr

val pf_nf_evar : Proofview.Goal.t -> constr -> constr

val pr_gls : Proofview.Goal.t -> Pp.t
