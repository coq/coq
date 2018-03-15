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
open EConstr
open Environ
open Evd

type core_unify_flags = {
  modulo_conv_on_closed_terms : Names.transparent_state option;
  use_metas_eagerly_in_conv_on_closed_terms : bool;
  use_evars_eagerly_in_conv_on_closed_terms : bool;
  modulo_delta : Names.transparent_state;
  modulo_delta_types : Names.transparent_state;
  check_applied_meta_types : bool;
  use_pattern_unification : bool;
  use_meta_bound_pattern_unification : bool;
  frozen_evars : Evar.Set.t;
  restrict_conv_on_strict_subterms : bool;
  modulo_betaiota : bool;
  modulo_eta : bool;
}

type unify_flags = {
  core_unify_flags : core_unify_flags;
  merge_unify_flags : core_unify_flags;
  subterm_unify_flags : core_unify_flags;
  allow_K_in_toplevel_higher_order_unification : bool;
  resolve_evars : bool
}

val default_core_unify_flags : unit -> core_unify_flags
val default_no_delta_core_unify_flags : unit -> core_unify_flags

val default_unify_flags : unit -> unify_flags
val default_no_delta_unify_flags : transparent_state -> unify_flags

val elim_flags : unit -> unify_flags
val elim_no_delta_flags : unit -> unify_flags

val is_keyed_unification : unit -> bool

(** The "unique" unification function *)
val w_unify :
  env -> evar_map -> conv_pb -> ?flags:unify_flags -> constr -> constr -> evar_map

(** [w_unify_to_subterm env m (c,t)] performs unification of [c] with a
   subterm of [t]. Constraints are added to [m] and the matched
   subterm of [t] is also returned. *)
val w_unify_to_subterm :
  env -> evar_map -> ?flags:unify_flags -> constr * constr -> evar_map * constr

val w_unify_to_subterm_all :
  env -> evar_map -> ?flags:unify_flags -> constr * constr -> (evar_map * constr) list

val w_unify_meta_types : env -> ?flags:unify_flags -> evar_map -> evar_map

(** [w_coerce_to_type env evd c ctyp typ] tries to coerce [c] of type
   [ctyp] so that its gets type [typ]; [typ] may contain metavariables *)
val w_coerce_to_type : env -> evar_map -> constr -> types -> types ->
  evar_map * constr

(* Looking for subterms in contexts at some occurrences, possibly with pattern*)

exception PatternNotFound

type prefix_of_inductive_support_flag = bool

type abstraction_request =
| AbstractPattern of prefix_of_inductive_support_flag * (types -> bool) * Names.Name.t * (evar_map * constr) * Locus.clause * bool
| AbstractExact of Names.Name.t * constr * types option * Locus.clause * bool

val finish_evar_resolution : ?flags:Pretyping.inference_flags ->
  env -> evar_map -> (evar_map * constr) -> evar_map * constr

type 'r abstraction_result =
  Names.Id.t * named_context_val *
    named_declaration list * Names.Id.t option *
    types * (evar_map * constr) option

val make_abstraction : env -> evar_map -> constr ->
  abstraction_request -> 'r abstraction_result

val pose_all_metas_as_evars : env -> evar_map -> constr -> evar_map * constr

(*i This should be in another module i*)

(** [abstract_list_all env evd t c l]
   abstracts the terms in l over c to get a term of type t
   (exported for inv.ml) *)
val abstract_list_all :
  env -> evar_map -> constr -> constr -> constr list -> evar_map * (constr * types)

(* For tracing *)

type metabinding = (metavariable * constr * (instance_constraint * instance_typing_status))

type subst0 =
  (evar_map *
    metabinding list *
      (Environ.env * existential * t) list)

val w_merge : env -> bool -> core_unify_flags -> subst0 -> evar_map

val unify_0 :            Environ.env ->
           Evd.evar_map ->
           Evd.conv_pb ->
           core_unify_flags ->
           types ->
           types ->
           subst0

val unify_0_with_initial_metas : 
           subst0 ->
           bool ->
           Environ.env ->
           Evd.conv_pb ->
           core_unify_flags ->
           types ->
           types ->
           subst0
