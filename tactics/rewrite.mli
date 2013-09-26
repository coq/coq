(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

type ('constr,'redexpr) strategy_ast = 
  | StratId | StratFail | StratRefl
  | StratUnary of string * ('constr,'redexpr) strategy_ast
  | StratBinary of string * ('constr,'redexpr) strategy_ast * ('constr,'redexpr) strategy_ast
  | StratConstr of 'constr * bool
  | StratTerms of 'constr list
  | StratHints of bool * string
  | StratEval of 'redexpr 
  | StratFold of 'constr

type evars = evar_map * Evar.Set.t (* goal evars, constraint evars *)

type rewrite_proof = 
  | RewPrf of constr * constr
  | RewCast of cast_kind

type rewrite_result_info = {
  rew_car : constr;
  rew_from : constr;
  rew_to : constr;
  rew_prf : rewrite_proof;
  rew_evars : evars;
}

type rewrite_result = rewrite_result_info option

type strategy = env -> Id.t list -> constr -> types ->
  constr option -> evars -> rewrite_result option

module Strategies :
sig
  val td : strategy -> strategy
  val hints : string -> strategy
end

val strategy_of_ast : (Glob_term.glob_constr * 'a, raw_red_expr) strategy_ast -> strategy

val map_strategy : ('a -> 'b) -> ('c -> 'd) ->
  ('a, 'c) strategy_ast -> ('b, 'd) strategy_ast

val cl_rewrite_clause_strat : strategy -> Id.t option -> tactic

val cl_rewrite_clause :
  interp_sign * (glob_constr_and_expr * glob_constr_and_expr bindings) ->
  bool -> Locus.occurrences -> Id.t option -> tactic

val cl_rewrite_clause_newtac' :
  interp_sign * (glob_constr_and_expr * glob_constr_and_expr bindings) ->
  bool -> Locus.occurrences -> Id.t option -> unit

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

val get_reflexive_proof : env -> evar_map -> constr -> constr -> constr

val get_symmetric_proof : env -> evar_map -> constr -> constr -> constr

val get_transitive_proof : env -> evar_map -> constr -> constr -> constr

val default_morphism :
  (types * constr option) option list * (types * types option) option ->
  constr -> constr * constr

val setoid_symmetry : tactic

val setoid_symmetry_in : Id.t -> tactic

val setoid_reflexivity : tactic

val setoid_transitivity : constr option -> tactic

val implify : Id.t -> tactic

val fold_match_tac : constr -> tactic

val fold_matches_tac : constr -> tactic

val myapply : Globnames.global_reference -> constr list -> tactic
