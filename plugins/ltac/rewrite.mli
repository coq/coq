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
open Environ
open EConstr
open Constrexpr
open Evd
open Tactypes
open Tacexpr
open Tacinterp

(** TODO: document and clean me! *)

type unary_strategy = 
    Subterms | Subterm | Innermost | Outermost
  | Bottomup | Topdown | Progress | Try | Any | Repeat

type binary_strategy = 
  | Compose | Choice

type ('constr,'redexpr) strategy_ast = 
  | StratId | StratFail | StratRefl
  | StratUnary of unary_strategy * ('constr,'redexpr) strategy_ast
  | StratBinary of binary_strategy 
    * ('constr,'redexpr) strategy_ast * ('constr,'redexpr) strategy_ast
  | StratConstr of 'constr * bool
  | StratTerms of 'constr list
  | StratHints of bool * string
  | StratEval of 'redexpr 
  | StratFold of 'constr

type rewrite_proof = 
  | RewPrf of constr * constr
  | RewCast of Constr.cast_kind

type evars = evar_map * Evar.Set.t (* goal evars, constraint evars *)

type rewrite_result_info = {
  rew_car : constr;
  rew_from : constr;
  rew_to : constr;
  rew_prf : rewrite_proof;
  rew_evars : evars;
}

type rewrite_result =
| Fail
| Identity
| Success of rewrite_result_info

type strategy

val strategy_of_ast : (glob_constr_and_expr, raw_red_expr) strategy_ast -> strategy

val map_strategy : ('a -> 'b) -> ('c -> 'd) ->
  ('a, 'c) strategy_ast -> ('b, 'd) strategy_ast

val pr_strategy : ('a -> Pp.t) -> ('b -> Pp.t) ->
  ('a, 'b) strategy_ast -> Pp.t

(** Entry point for user-level "rewrite_strat" *)
val cl_rewrite_clause_strat : strategy -> Id.t option -> unit Proofview.tactic

(** Entry point for user-level "setoid_rewrite" *)
val cl_rewrite_clause :
  interp_sign * (glob_constr_and_expr * glob_constr_and_expr bindings) ->
  bool -> Locus.occurrences -> Id.t option -> unit Proofview.tactic

val is_applied_rewrite_relation :
  env -> evar_map -> rel_context -> constr -> types option

val declare_relation : ?locality:bool ->
  ?binders:local_binder_expr list -> constr_expr -> constr_expr -> Id.t ->
  constr_expr option -> constr_expr option -> constr_expr option -> unit

val add_setoid :
  bool -> local_binder_expr list -> constr_expr -> constr_expr -> constr_expr ->
  Id.t -> unit

val add_morphism_infer : bool -> constr_expr -> Id.t -> unit

val add_morphism :
  bool -> local_binder_expr list -> constr_expr -> constr_expr -> Id.t -> unit

val get_reflexive_proof : env -> evar_map -> constr -> constr -> evar_map * constr

val get_symmetric_proof : env -> evar_map -> constr -> constr -> evar_map * constr

val get_transitive_proof : env -> evar_map -> constr -> constr -> evar_map * constr

val default_morphism :
  (types * constr option) option list * (types * types option) option ->
  constr -> constr * constr

val setoid_symmetry : unit Proofview.tactic

val setoid_symmetry_in : Id.t -> unit Proofview.tactic

val setoid_reflexivity : unit Proofview.tactic

val setoid_transitivity : constr option -> unit Proofview.tactic


val apply_strategy :
  strategy ->
  Environ.env ->
  Names.Id.Set.t ->
  constr ->
  bool * constr ->
  evars -> rewrite_result
