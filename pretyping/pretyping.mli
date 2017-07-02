(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file implements type inference. It maps [glob_constr]
   (i.e. untyped terms whose names are located) to [constr]. In
   particular, it drives complex pattern-matching problems ("match")
   into elementary ones, insertion of coercions and resolution of
   implicit arguments. *)

open Term
open Environ
open Evd
open EConstr
open Glob_term
open Evarutil
open Misctypes

(** An auxiliary function for searching for fixpoint guard indexes *)

val search_guard :
  ?loc:Loc.t -> env -> int list list -> rec_declaration -> int array

type typing_constraint = OfType of types | IsType | WithoutTypeConstraint

type glob_constr_ltac_closure = ltac_var_map * glob_constr
type pure_open_constr = evar_map * constr

type inference_hook = env -> evar_map -> evar -> evar_map * constr

type inference_flags = {
  use_typeclasses : bool;
  solve_unification_constraints : bool;
  use_hook : inference_hook option;
  fail_evar : bool;
  expand_evars : bool
}

val default_inference_flags : bool -> inference_flags

val no_classes_no_fail_inference_flags : inference_flags

val all_no_fail_flags : inference_flags

val all_and_fail_flags : inference_flags

(** Allow references to syntactically nonexistent variables (i.e., if applied on an inductive) *)
val allow_anonymous_refs : bool ref
  
(** Generic calls to the interpreter from glob_constr to open_constr;
    by default, inference_flags tell to use type classes and
    heuristics (but no external tactic solver hooks), as well as to
    ensure that conversion problems are all solved and expand evars,
    but unresolved evars can remain. The difference is in whether the
    evar_map is modified explicitly or by side-effect. *)

val understand_tcc : ?flags:inference_flags -> env -> evar_map ->
  ?expected_type:typing_constraint -> glob_constr -> evar_map * constr

val understand_tcc_evars : ?flags:inference_flags -> env -> evar_map ref ->
  ?expected_type:typing_constraint -> glob_constr -> constr

(** More general entry point with evars from ltac *)

(** Generic call to the interpreter from glob_constr to constr

    In [understand_ltac flags sigma env ltac_env constraint c],

    flags: tell how to manage evars
    sigma: initial set of existential variables (typically current goals)
    ltac_env: partial substitution of variables (used for the tactic language)
    constraint: tell if interpreted as a possibly constrained term or a type
*)

val understand_ltac : inference_flags ->
  env -> evar_map -> ltac_var_map ->
  typing_constraint -> glob_constr -> pure_open_constr

(** Standard call to get a constr from a glob_constr, resolving
    implicit arguments and coercions, and compiling pattern-matching;
    the default inference_flags tells to use type classes and
    heuristics (but no external tactic solver hook), as well as to
    ensure that conversion problems are all solved and that no
    unresolved evar remains, expanding evars. *)

val understand : ?flags:inference_flags -> ?expected_type:typing_constraint ->
  env -> evar_map -> glob_constr -> Constr.constr Evd.in_evar_universe_context

(** Idem but returns the judgment of the understood term *)

val understand_judgment : env -> evar_map -> 
  glob_constr -> unsafe_judgment Evd.in_evar_universe_context

(** Idem but do not fail on unresolved evars (type cl*)
val understand_judgment_tcc : env -> evar_map ref ->
  glob_constr -> unsafe_judgment

val type_uconstr :
  ?flags:inference_flags ->
  ?expected_type:typing_constraint ->
  Geninterp.interp_sign -> Glob_term.closed_glob_constr -> constr Tactypes.delayed_open

(** Trying to solve remaining evars and remaining conversion problems
    possibly using type classes, heuristics, external tactic solver
    hook depending on given flags. *)
(* For simplicity, it is assumed that current map has no other evars
   with candidate and no other conversion problems that the one in
   [pending], however, it can contain more evars than the pending ones. *)

val solve_remaining_evars : inference_flags ->
  env -> (* current map *) evar_map -> (* initial map *) evar_map -> evar_map

(** Checking evars and pending conversion problems are all solved,
    reporting an appropriate error message *)

val check_evars_are_solved :
  env -> (* current map: *) evar_map -> (* initial map: *) evar_map -> unit

(** [check_evars env initial_sigma extended_sigma c] fails if some
   new unresolved evar remains in [c] *)
val check_evars : env -> evar_map -> evar_map -> constr -> unit

(**/**)
(** Internal of Pretyping... *)
val pretype :
  int -> bool -> type_constraint -> env -> evar_map ref ->
  ltac_var_map -> glob_constr -> unsafe_judgment

val pretype_type :
  int -> bool -> val_constraint -> env -> evar_map ref ->
  ltac_var_map -> glob_constr -> unsafe_type_judgment

val ise_pretype_gen :
  inference_flags -> env -> evar_map ->
  ltac_var_map -> typing_constraint -> glob_constr -> evar_map * constr

(**/**)

(** To embed constr in glob_constr *)

val interp_sort : ?loc:Loc.t -> evar_map -> glob_sort -> evar_map * sorts
val interp_elimination_sort : glob_sort -> sorts_family

val register_constr_interp0 :
  ('r, 'g, 't) Genarg.genarg_type ->
    (unbound_ltac_var_map -> env -> evar_map -> types -> 'g -> constr * evar_map) -> unit
