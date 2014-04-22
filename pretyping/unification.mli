(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Environ
open Evd

type unify_flags = {
  modulo_conv_on_closed_terms : Names.transparent_state option;
  use_metas_eagerly_in_conv_on_closed_terms : bool;
  modulo_delta : Names.transparent_state;
  modulo_delta_types : Names.transparent_state;
  modulo_delta_in_merge : Names.transparent_state option;
  check_applied_meta_types : bool;
  resolve_evars : bool;
  use_pattern_unification : bool;
  use_meta_bound_pattern_unification : bool;
  frozen_evars : Evar.Set.t;
  restrict_conv_on_strict_subterms : bool;
  modulo_betaiota : bool;
  modulo_eta : bool;
  allow_K_in_toplevel_higher_order_unification : bool
}

val default_unify_flags : unify_flags
val default_no_delta_unify_flags : unify_flags

val elim_flags : unify_flags
val elim_no_delta_flags : unify_flags

(** The "unique" unification fonction *)
val w_unify :
  env -> evar_map -> conv_pb -> ?flags:unify_flags -> constr -> constr -> evar_map

(** [w_unify_to_subterm env (c,t) m] performs unification of [c] with a
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

(*i This should be in another module i*)

(** [abstract_list_all env evd t c l]
   abstracts the terms in l over c to get a term of type t
   (exported for inv.ml) *)
val abstract_list_all :
  env -> evar_map -> constr -> constr -> constr list -> constr * types


(* For tracing *)

val w_merge : env -> bool -> unify_flags -> evar_map *
  (metavariable * constr * (instance_constraint * instance_typing_status)) list *
  (env * types pexistential * types) list -> evar_map

val unify_0 :            Environ.env ->
           Evd.evar_map ->
           Evd.conv_pb ->
           unify_flags ->
           Term.types ->
           Term.types ->
           Evd.evar_map * Evd.metabinding list *
           (Environ.env * Term.types Term.pexistential * Term.constr) list

