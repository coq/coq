(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Environ
open Evd
(*i*)

type unify_flags = {
  modulo_conv_on_closed_terms : Names.transparent_state option;
  use_metas_eagerly : bool;
  modulo_delta : Names.transparent_state;
  resolve_evars : bool;
  use_evars_pattern_unification : bool
}

val default_unify_flags : unify_flags
val default_no_delta_unify_flags : unify_flags

(* The "unique" unification fonction *)
val w_unify :
  bool -> env -> conv_pb -> ?flags:unify_flags -> constr -> constr -> evar_map -> evar_map

(* [w_unify_to_subterm env (c,t) m] performs unification of [c] with a
   subterm of [t]. Constraints are added to [m] and the matched
   subterm of [t] is also returned. *)
val w_unify_to_subterm :
  env -> ?flags:unify_flags -> constr * constr -> evar_map -> evar_map * constr

val w_unify_to_subterm_all :
  env -> ?flags:unify_flags -> constr * constr -> evar_map -> (evar_map * constr) list

val w_unify_meta_types : env -> ?flags:unify_flags -> evar_map -> evar_map

(* [w_coerce_to_type env evd c ctyp typ] tries to coerce [c] of type
   [ctyp] so that its gets type [typ]; [typ] may contain metavariables *)
val w_coerce_to_type : env -> evar_map -> constr -> types -> types ->
  evar_map * constr

(*i This should be in another module i*)

(* [abstract_list_all env evd t c l]                       *)
(* abstracts the terms in l over c to get a term of type t *)
(* (exported for inv.ml) *)
val abstract_list_all :
  env -> evar_map -> constr -> constr -> constr list -> constr
