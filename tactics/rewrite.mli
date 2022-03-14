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
open Environ
open EConstr
open Evd
open Tactypes

(** TODO: document and clean me! *)

exception RewriteFailure of Environ.env * Evd.evar_map * Pretype_errors.pretype_error

type unary_strategy =
    Subterms | Subterm | Innermost | Outermost
  | Bottomup | Topdown | Progress | Try | Any | Repeat

type binary_strategy =
  | Compose

type nary_strategy = Choice

type ('constr,'redexpr) strategy_ast =
  | StratId | StratFail | StratRefl
  | StratUnary of unary_strategy * ('constr,'redexpr) strategy_ast
  | StratBinary of
      binary_strategy * ('constr,'redexpr) strategy_ast * ('constr,'redexpr) strategy_ast
  | StratNAry of nary_strategy * ('constr,'redexpr) strategy_ast list
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

val strategy_of_ast : (Glob_term.glob_constr * constr delayed_open, Redexpr.red_expr delayed_open) strategy_ast -> strategy

val map_strategy : ('a -> 'b) -> ('c -> 'd) ->
  ('a, 'c) strategy_ast -> ('b, 'd) strategy_ast

val pr_strategy : ('a -> Pp.t) -> ('b -> Pp.t) ->
  ('a, 'b) strategy_ast -> Pp.t

(** Entry point for user-level "rewrite_strat" *)
val cl_rewrite_clause_strat : strategy -> Id.t option -> unit Proofview.tactic

(** Entry point for user-level "setoid_rewrite" *)
val cl_rewrite_clause :
  EConstr.t with_bindings delayed_open ->
  bool -> Locus.occurrences -> Id.t option -> unit Proofview.tactic

val is_applied_rewrite_relation :
  env -> evar_map -> rel_context -> constr -> types option

val get_reflexive_proof : env -> evar_map -> constr -> constr -> evar_map * constr

val get_symmetric_proof : env -> evar_map -> constr -> constr -> evar_map * constr

val get_transitive_proof : env -> evar_map -> constr -> constr -> evar_map * constr

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

module Internal :
sig
val build_signature :
  Environ.env -> Evd.evar_map -> constr ->
  (types * types option) option list ->
  (types * types option) option ->
  Evd.evar_map * constr * (constr * t option) list
val build_morphism_signature : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Evd.evar_map * t
val default_morphism : Environ.env -> Evd.evar_map ->
  (types * types option) option list *
  (types * types option) option ->
  constr -> constr * t
end
