(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr
open Environ
open Constrexpr
open Tacexpr
open Misctypes
open Evd
open Proof_type
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
  | RewCast of cast_kind

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

type 'a pure_strategy = 'a -> Environ.env -> Id.t list -> constr -> types ->
  (bool (* prop *) * constr option) -> evars -> 'a * rewrite_result

type strategy = unit pure_strategy

val strategy_of_ast : (glob_constr_and_expr, raw_red_expr) strategy_ast -> strategy

val map_strategy : ('a -> 'b) -> ('c -> 'd) ->
  ('a, 'c) strategy_ast -> ('b, 'd) strategy_ast

(** Entry point for user-level "rewrite_strat" *)
val cl_rewrite_clause_strat : strategy -> Id.t option -> tactic

(** Entry point for user-level "setoid_rewrite" *)
val cl_rewrite_clause :
  interp_sign * (glob_constr_and_expr * glob_constr_and_expr bindings) ->
  bool -> Locus.occurrences -> Id.t option -> tactic

val is_applied_rewrite_relation :
  env -> evar_map -> Context.rel_context -> constr -> types option

val declare_relation :
  ?binders:local_binder list -> constr_expr -> constr_expr -> Id.t ->
  constr_expr option -> constr_expr option -> constr_expr option -> unit

val add_setoid :
  bool -> local_binder list -> constr_expr -> constr_expr -> constr_expr ->
  Id.t -> unit

val add_morphism_infer : bool -> constr_expr -> Id.t -> unit

val add_morphism :
  bool -> local_binder list -> constr_expr -> constr_expr -> Id.t -> unit

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
  Names.Id.t list ->
  Term.constr ->
  bool * Term.constr ->
  evars -> rewrite_result
