(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file defines clausenv, which is a deprecated way to handle open terms
    in the proof engine. This API is legacy. *)

open Constr
open Environ
open Evd
open EConstr
open Unification
open Tactypes

(** {6 The Type of Constructions clausale environments.} *)

type clausenv

val clenv_evd : clausenv -> Evd.evar_map
val clenv_meta_list : clausenv -> Meta.t

(* Ad-hoc primitives *)
val update_clenv_evd : clausenv -> evar_map -> Meta.t -> clausenv
val clenv_strip_proj_params : clausenv -> clausenv
val clenv_refresh : env -> evar_map -> UnivGen.sort_context_set option -> clausenv -> clausenv
val clenv_arguments : clausenv -> metavariable list

(** subject of clenv (instantiated) *)
val clenv_value     : clausenv -> constr

(** type of clenv (instantiated) *)
val clenv_type      : clausenv -> types

val mk_clenv_from : env -> evar_map -> EConstr.constr * EConstr.types -> clausenv
val mk_clenv_from_n : env -> evar_map -> int -> EConstr.constr * EConstr.types -> clausenv

(** {6 linking of clenvs } *)

val clenv_instantiate : ?flags:unify_flags -> ?submetas:(metavariable list * Unification.Meta.t) ->
  metavariable -> clausenv -> (constr * types) -> clausenv

(** {6 Bindings } *)

(** bindings where the key is the position in the template of the
   clenv (dependent or not). Positions can be negative meaning to
   start from the rightmost argument of the template. *)
val clenv_independent : clausenv -> metavariable list
val clenv_missing : clausenv -> Names.Name.t list * int

(** start with a clenv to refine with a given term with bindings *)

(** the arity of the lemma is fixed
   the optional int tells how many prods of the lemma have to be used
   use all of them if None *)
val make_clenv_binding_apply :
  env -> evar_map -> int option -> EConstr.constr * EConstr.constr -> constr bindings ->
   clausenv

val make_clenv_binding :
  env -> evar_map -> EConstr.constr * EConstr.constr -> constr bindings -> clausenv

(** if the clause is a product, add an extra meta for this product *)
val clenv_push_prod : clausenv -> (metavariable * bool * clausenv) option

(** {6 Clenv tactics} *)

val unify : ?flags:unify_flags -> cv_pb:Conversion.conv_pb -> constr -> unit Proofview.tactic
val res_pf : ?with_evars:bool -> ?with_classes:bool -> ?flags:unify_flags -> clausenv -> unit Proofview.tactic
val case_pf : ?with_evars:bool ->
  dep:bool -> (constr * types) -> unit Proofview.tactic

val clenv_pose_dependent_evars : ?with_evars:bool -> clausenv -> clausenv

(** {6 Pretty-print (debug only) } *)
val pr_clenv : clausenv -> Pp.t

module Internal :
sig

(** The legacy refiner. Do not use. *)
val refiner : clausenv -> unit Proofview.tactic
[@@ocaml.deprecated]

end
