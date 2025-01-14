(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

open Names
open Environ
open Evd
open EConstr
open Glob_term
open Ltac_pretype

val add_bidirectionality_hint : GlobRef.t -> int -> unit
(** A bidirectionality hint `n` for a global `g` tells the pretyper to use
    typing information from the context after typing the `n` for arguments of an
    application of `g`. *)

val get_bidirectionality_hint : GlobRef.t -> int option

val clear_bidirectionality_hint : GlobRef.t -> unit

(** An auxiliary function for searching for fixpoint guard indices *)

(* Tells the possible indices liable to guard a fixpoint *)
type possible_fix_indices = int list list

(* Tells if possibly a cofixpoint or a fixpoint over the given list of possible indices *)
type possible_guard = {
  possibly_cofix : bool;
  possible_fix_indices : possible_fix_indices;
} (* Note: if no fix indices are given, it has to be a cofix *)

val search_guard :
  ?loc:Loc.t -> ?evars:CClosure.evar_handler -> env ->
  possible_guard -> Constr.rec_declaration -> int array option

val search_fix_guard : (* For Fixpoints only *)
  ?loc:Loc.t -> ?evars:CClosure.evar_handler -> env ->
  possible_fix_indices -> Constr.rec_declaration -> int array

val esearch_guard :
  ?loc:Loc.t -> env -> evar_map -> possible_guard ->
  EConstr.rec_declaration -> int array option

val esearch_fix_guard : (* For Fixpoints only *)
  ?loc:Loc.t -> env -> evar_map -> possible_fix_indices ->
  EConstr.rec_declaration -> int array

val esearch_cofix_guard : ?loc:Loc.t -> env -> evar_map -> EConstr.rec_declaration -> unit

type typing_constraint =
  | IsType (** Necessarily a type *)
  | OfType of types (** A term of the expected type *)
  | WithoutTypeConstraint (** A term of unknown expected type *)

type use_typeclasses = NoUseTC | UseTCForConv | UseTC
(** Typeclasses are used in 2 ways:

- through the "Typeclass Resolution For Conversion" option, if a
  conversion problem fails we try again after resolving typeclasses
  (UseTCForConv and UseTC)
- after pretyping we resolve typeclasses (UseTC) (in [solve_remaining_evars])
*)

type inference_flags = {
  use_coercions : bool;
  use_typeclasses : use_typeclasses;
  solve_unification_constraints : bool;
  fail_evar : bool;
  expand_evars : bool;
  program_mode : bool;
  polymorphic : bool;
  undeclared_evars_patvars : bool;
  patvars_abstract : bool;
  unconstrained_sorts : bool;
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

val understand_ltac_ty : inference_flags ->
  env -> evar_map -> ltac_var_map ->
  typing_constraint -> glob_constr -> evar_map * EConstr.t * EConstr.types

(** Standard call to get a constr from a glob_constr, resolving
    implicit arguments and coercions, and compiling pattern-matching;
    the default inference_flags tells to use type classes and
    heuristics (but no external tactic solver hook), as well as to
    ensure that conversion problems are all solved and that no
    unresolved evar remains, expanding evars. *)
val understand : ?flags:inference_flags -> ?expected_type:typing_constraint ->
  env -> evar_map -> glob_constr -> constr Evd.in_ustate

val understand_uconstr :
  ?flags:inference_flags -> ?expected_type:typing_constraint ->
  env -> evar_map -> Ltac_pretype.closed_glob_constr -> evar_map * EConstr.t

(** [hook env sigma ev] returns [Some (sigma', term)] if [ev] can be
   instantiated with a solution, [None] otherwise. Used to extend
   [solve_remaining_evars] below. *)
type inference_hook = env -> evar_map -> Evar.t -> (evar_map * constr) option

(** Trying to solve remaining evars and remaining conversion problems
    possibly using type classes, heuristics, external tactic solver
    hook depending on given flags. *)
(* For simplicity, it is assumed that current map has no other evars
   with candidate and no other conversion problems that the one in
   [pending], however, it can contain more evars than the pending ones. *)
val solve_remaining_evars : ?hook:inference_hook -> inference_flags ->
  env -> ?initial:evar_map -> (* current map *) evar_map -> evar_map

(** Checking evars and pending conversion problems are all solved,
    reporting an appropriate error message *)

val check_evars_are_solved :
  program_mode:bool -> env -> ?initial:evar_map -> (* current map: *) evar_map -> unit

(** [check_evars env ?initial sigma c] fails if some unresolved evar
   remains in [c] which isn't in [initial] (any unresolved evar if
   [initial] not provided) *)
val check_evars : env -> ?initial:evar_map -> evar_map -> constr -> unit

(**/**)
(** Internal of Pretyping... *)
val ise_pretype_gen :
  inference_flags -> env -> evar_map ->
  ltac_var_map -> typing_constraint -> glob_constr -> evar_map * constr * types

(** {6 Open-recursion style pretyper} *)

type pretype_flags = {
  poly : bool;
  resolve_tc : bool;
  program_mode : bool;
  use_coercions : bool;
  undeclared_evars_patvars : bool;
  patvars_abstract : bool;
  unconstrained_sorts : bool;
}

type 'a pretype_fun = ?loc:Loc.t -> flags:pretype_flags -> Evardefine.type_constraint -> GlobEnv.t -> evar_map -> evar_map * 'a

type pretyper = {
  pretype_ref : pretyper -> GlobRef.t * glob_instance option -> unsafe_judgment pretype_fun;
  pretype_var : pretyper -> Id.t -> unsafe_judgment pretype_fun;
  pretype_evar : pretyper -> existential_name CAst.t * (lident * glob_constr) list -> unsafe_judgment pretype_fun;
  pretype_patvar : pretyper -> Evar_kinds.matching_var_kind -> unsafe_judgment pretype_fun;
  pretype_app : pretyper -> glob_constr * glob_constr list -> unsafe_judgment pretype_fun;
  pretype_proj : pretyper -> (Constant.t * glob_instance option) * glob_constr list * glob_constr -> unsafe_judgment pretype_fun;
  pretype_lambda : pretyper -> Name.t * binding_kind * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_prod : pretyper -> Name.t * binding_kind * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_letin : pretyper -> Name.t * glob_constr * glob_constr option * glob_constr -> unsafe_judgment pretype_fun;
  pretype_cases : pretyper -> Constr.case_style * glob_constr option * tomatch_tuples * cases_clauses -> unsafe_judgment pretype_fun;
  pretype_lettuple : pretyper -> Name.t list * (Name.t * glob_constr option) * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_if : pretyper -> glob_constr * (Name.t * glob_constr option) * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_rec : pretyper -> glob_fix_kind * Id.t array * glob_decl list array * glob_constr array * glob_constr array -> unsafe_judgment pretype_fun;
  pretype_sort : pretyper -> glob_sort -> unsafe_judgment pretype_fun;
  pretype_hole : pretyper -> Evar_kinds.glob_evar_kind -> unsafe_judgment pretype_fun;
  pretype_genarg : pretyper -> Genarg.glob_generic_argument -> unsafe_judgment pretype_fun;
  pretype_cast : pretyper -> glob_constr * Constr.cast_kind option * glob_constr -> unsafe_judgment pretype_fun;
  pretype_int : pretyper -> Uint63.t -> unsafe_judgment pretype_fun;
  pretype_float : pretyper -> Float64.t -> unsafe_judgment pretype_fun;
  pretype_string : pretyper -> Pstring.t -> unsafe_judgment pretype_fun;
  pretype_array : pretyper -> glob_instance option * glob_constr array * glob_constr * glob_constr -> unsafe_judgment pretype_fun;
  pretype_type : pretyper -> glob_constr -> unsafe_type_judgment pretype_fun;
}
(** Type of pretyping algorithms in open-recursion style. A typical way to
    implement a pretyping variant is to inherit from some pretyper using
    record inheritance and replacing particular fields with the [where] clause.
    Recursive calls to the subterms should call the [pretyper] provided as the
    first argument to the function. This object can be turned in an actual
    pretyping function through the {!eval_pretyper} function below. *)

val default_pretyper : pretyper
(** Rocq vanilla pretyper. *)

val eval_pretyper : pretyper -> flags:pretype_flags -> Evardefine.type_constraint -> GlobEnv.t -> evar_map -> glob_constr -> evar_map * unsafe_judgment
