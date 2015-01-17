(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context
open Environ
open Glob_term
open Termops
open Mod_subst
open Misctypes
open Evd

(** Should we keep details of universes during detyping ? *)
val print_universes : bool ref

(** If true, prints full local context of evars *)
val print_evar_arguments : bool ref

val subst_cases_pattern : substitution -> cases_pattern -> cases_pattern

val subst_glob_constr : substitution -> glob_constr -> glob_constr

(** [detype isgoal avoid ctx c] turns a closed [c], into a glob_constr 
   de Bruijn indexes are turned to bound names, avoiding names in [avoid] 
   [isgoal] tells if naming must avoid global-level synonyms as intro does 
   [ctx] gives the names of the free variables *)

val detype_names : bool -> Id.t list -> names_context -> env -> evar_map -> constr -> glob_constr

val detype : ?lax:bool -> bool -> Id.t list -> env -> evar_map -> constr -> glob_constr

val detype_case :
  bool -> (constr -> glob_constr) ->
  (constructor array -> bool list array -> constr array ->
    (Loc.t * Id.t list * cases_pattern list * glob_constr) list) ->
  (constr -> bool list -> bool) ->
  Id.t list -> inductive * case_style * bool list array * bool list ->
    constr option -> constr -> constr array -> glob_constr

val detype_sort : evar_map -> sorts -> glob_sort

val detype_rel_context : ?lax:bool -> constr option -> Id.t list -> (names_context * env) -> 
  evar_map -> rel_context -> glob_decl list

val detype_closed_glob : ?lax:bool -> bool -> Id.t list -> env -> evar_map -> closed_glob_constr -> glob_constr

(** look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_displayed  : env -> constr -> Id.t -> int option
val lookup_index_as_renamed : env -> constr -> int -> int option

val set_detype_anonymous : (Loc.t -> int -> glob_constr) -> unit
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
    val encode : Libnames.reference -> Names.inductive
    val member_message : Pp.std_ppcmds -> bool -> Pp.std_ppcmds
    val field : string
    val title : string
  end) ->
    sig
      type t = Names.inductive
      val compare : t -> t -> int
      val encode : Libnames.reference -> Names.inductive
      val subst : substitution -> t -> t
      val printer : t -> Pp.std_ppcmds
      val key : Goptions.option_name
      val title : string
      val member_message : t -> bool -> Pp.std_ppcmds
      val synchronous : bool
    end
