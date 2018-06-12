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
open Glob_term
open Termops
open Mod_subst
open Evd
open Ltac_pretype

type _ delay =
| Now : 'a delay
| Later : [ `thunk ] delay

(** Should we keep details of universes during detyping ? *)
val print_universes : bool ref

(** If true, prints full local context of evars *)
val print_evar_arguments : bool ref

(** If true, contract branches with same r.h.s. and same matching
    variables in a disjunctive pattern *)
val print_factorize_match_patterns : bool ref

(** If true and the last non unique clause of a "match" is a
    variable-free disjunctive pattern, turn it into a catch-call case *)
val print_allow_match_default_clause : bool ref

val subst_cases_pattern : substitution -> cases_pattern -> cases_pattern

val subst_glob_constr : substitution -> glob_constr -> glob_constr

val factorize_eqns : 'a cases_clauses_g -> 'a disjunctive_cases_clauses_g

(** [detype isgoal avoid ctx c] turns a closed [c], into a glob_constr 
   de Bruijn indexes are turned to bound names, avoiding names in [avoid] 
   [isgoal] tells if naming must avoid global-level synonyms as intro does 
   [ctx] gives the names of the free variables *)

val detype_names : bool -> Id.Set.t -> names_context -> env -> evar_map -> constr -> glob_constr

val detype : 'a delay -> ?lax:bool -> bool -> Id.Set.t -> env -> evar_map -> constr -> 'a glob_constr_g

val detype_sort : evar_map -> Sorts.t -> glob_sort

val detype_rel_context : 'a delay -> ?lax:bool -> constr option -> Id.Set.t -> (names_context * env) -> 
  evar_map -> rel_context -> 'a glob_decl_g list

val share_pattern_names :
  (Id.Set.t -> names_context -> 'c -> Pattern.constr_pattern -> 'a) -> int ->
  (Name.t * Decl_kinds.binding_kind * 'b option * 'a) list ->
  Id.Set.t -> names_context -> 'c -> Pattern.constr_pattern ->
  Pattern.constr_pattern ->
  (Name.t * Decl_kinds.binding_kind * 'b option * 'a) list * 'a * 'a

val detype_closed_glob : ?lax:bool -> bool -> Id.Set.t -> env -> evar_map -> closed_glob_constr -> glob_constr

(** look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_displayed  : env -> evar_map -> constr -> Id.t -> int option
val lookup_index_as_renamed : env -> evar_map -> constr -> int -> int option

(* XXX: This is a hack and should go away *)
val set_detype_anonymous : (?loc:Loc.t -> int -> Id.t) -> unit

val force_wildcard : unit -> bool
val synthetize_type : unit -> bool

(** Utilities to transform kernel cases to simple pattern-matching problem *)

val it_destRLambda_or_LetIn_names : bool list -> glob_constr -> Name.t list * glob_constr
val simple_cases_matrix_of_branches :
  inductive -> (int * bool list * glob_constr) list -> cases_clauses
val return_type_of_predicate :
  inductive -> bool list -> glob_constr -> predicate_pattern * glob_constr option

val subst_genarg_hook :
  (substitution -> Genarg.glob_generic_argument -> Genarg.glob_generic_argument) Hook.t

module PrintingInductiveMake :
  functor (Test : sig
    val encode : Libnames.qualid -> Names.inductive
    val member_message : Pp.t -> bool -> Pp.t
    val field : string
    val title : string
  end) ->
    sig
      type t = Names.inductive
      val compare : t -> t -> int
      val encode : Libnames.qualid -> Names.inductive
      val subst : substitution -> t -> t
      val printer : t -> Pp.t
      val key : Goptions.option_name
      val title : string
      val member_message : t -> bool -> Pp.t
      val synchronous : bool
    end
