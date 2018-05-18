(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file implements type inference. It maps [glob_constr]
   (i.e. untyped terms whose names are located) to [constr]. In
   particular, it drives complex pattern-matching problems ("match")
   into elementary ones, insertion of coercions and resolution of
   implicit arguments. *)

open Environ
open Evd
open EConstr
open Glob_term
open Ltac_pretype
open Evardefine

val interp_known_glob_level : ?loc:Loc.t -> Evd.evar_map ->
  glob_level -> Univ.Level.t

(** An auxiliary function for searching for fixpoint guard indexes *)

val search_guard :
  ?loc:Loc.t -> env -> int list list -> Constr.rec_declaration -> int array

type typing_constraint = OfType of types | IsType | WithoutTypeConstraint

type inference_hook = env -> evar_map -> Evar.t -> evar_map * constr

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

(** Generic calls to the interpreter from glob_constr to open_constr;
    by default, inference_flags tell to use type classes and
    heuristics (but no external tactic solver hooks), as well as to
    ensure that conversion problems are all solved and expand evars,
    but unresolved evars can remain. The difference is in whether the
    evar_map is modified explicitly or by side-effect. *)

val understand_tcc : ?flags:inference_flags -> env -> evar_map ->
  ?expected_type:typing_constraint -> glob_constr -> evar_map * constr

(** As [understand_tcc] but also returns the type of the elaborated term.
    The [expand_evars] flag is not applied to the type (only to the term). *)
val understand_tcc_ty : ?flags:inference_flags -> env -> evar_map ->
  ?expected_type:typing_constraint -> glob_constr -> evar_map * constr * types

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
  typing_constraint -> glob_constr -> evar_map * EConstr.t

(** Standard call to get a constr from a glob_constr, resolving
    implicit arguments and coercions, and compiling pattern-matching;
    the default inference_flags tells to use type classes and
    heuristics (but no external tactic solver hook), as well as to
    ensure that conversion problems are all solved and that no
    unresolved evar remains, expanding evars. *)
val understand : ?flags:inference_flags -> ?expected_type:typing_constraint ->
  env -> evar_map -> glob_constr -> constr Evd.in_evar_universe_context

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
  ltac_var_map -> typing_constraint -> glob_constr -> evar_map * constr * types

(**/**)

(** To embed constr in glob_constr *)

val register_constr_interp0 :
  ('r, 'g, 't) Genarg.genarg_type ->
    (unbound_ltac_var_map -> env -> evar_map -> types -> 'g -> constr * evar_map) -> unit
