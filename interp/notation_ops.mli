(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Notation_term
open Glob_term
open Constrexpr

(** Constr default entries *)

(* Equivalent to an entry "in constr at level 0"; used for coercion to constr *)
val constr_lowest_level : Constrexpr.notation_entry_level

(* Equivalent to "x constr" in a subentry, at highest level *)
val constr_some_level : Constrexpr.notation_entry_relative_level

(** {5 Utilities about [notation_constr]} *)

val eq_notation_constr : Id.t list * Id.t list -> notation_constr -> notation_constr -> bool

val strictly_finer_notation_constr : Id.t list * Id.t list -> notation_constr -> notation_constr -> bool
(** Tell if [t1] is a strict refinement of [t2]
    (this is a partial order and returning [false] does not mean that
    [t2] is finer than [t1]) *)

val strictly_finer_interpretation_than : interpretation -> interpretation -> bool
(** Tell if a notation interpretation is strictly included in another one *)

val finer_interpretation_than : _ interpretation_gen -> _ interpretation_gen -> bool
(** Tell if a notation interpretation is included in another one *)

(** Substitution of kernel names in interpretation data                *)

val subst_interpretation :
  Mod_subst.substitution -> interpretation -> interpretation

(** Name of the special identifier used to encode recursive notations  *)

val ldots_var : Id.t

(** {5 Translation back and forth between [glob_constr] and [notation_constr]} *)

(** Translate a [glob_constr] into a notation given the list of variables
    bound by the notation; also interpret recursive patterns           *)

val notation_constr_of_glob_constr : notation_interp_env ->
  glob_constr -> notation_constr * reversibility_status

(** Re-interpret a notation as a [glob_constr], taking care of binders *)

type 'a binder_status_fun = {
  no : 'a -> 'a;
  restart_prod : 'a -> 'a;
  restart_lambda : 'a -> 'a;
  switch_prod : 'a -> 'a;
  switch_lambda : 'a -> 'a;
  slide : 'a -> 'a;
}

val apply_cases_pattern : ?loc:Loc.t ->
  (Id.t list * cases_pattern_disjunction) * Id.t -> glob_constr -> glob_constr

val glob_constr_of_notation_constr_with_binders : ?loc:Loc.t ->
  ('a -> Name.t -> glob_constr option -> 'a * ((Id.t list * cases_pattern_disjunction) * Id.t) option * Name.t * Glob_term.binding_kind * glob_constr option) ->
  ('a -> notation_constr -> glob_constr) -> ?h:'a binder_status_fun ->
  'a -> notation_constr -> glob_constr

val glob_constr_of_notation_constr : ?loc:Loc.t -> notation_constr -> glob_constr

val pr_notation_info :
  (Glob_term.glob_constr -> Pp.t) -> Constrexpr.notation_key -> Notation_term.notation_constr -> Pp.t

val dummy_subscopes : extended_subscopes * notation_var_binders

(** {5 Matching a notation pattern against a [glob_constr]} *)

(** [match_notation_constr] matches a [glob_constr] against a notation
    interpretation; raise [No_match] if the matching fails   *)

exception No_match

(** When term matching a rule is found, with_vars informs about the
    set of actual binder names of this term and the pairs (x,y) of
    (notation-unbound) binder name [x] of the pattern and
    corresponding binder name [y] in the term; e.g. when matching the
    term "fun '((y,z) as c) b => t" against the pattern "fun x a => u"
    (when x is not bound in the notation) the actual binder names include
    [c,y,z,b] and the matching pairs are [(x,c);(b,a)] *)
type 'a with_vars = Id.Set.t * (Name.t * Id.t) list * 'a

(** Instances of notation variables, with their type as interpreted in
    a term; also, when a variable is used both as term and binder, it
    is represented as a a pattern *)
type 'a glob_constr_notation_substitution =
  ('a glob_constr_g with_vars, 'a cases_pattern_disjunction_g with_vars, 'a extended_glob_local_binder_g list with_vars) notation_arg_type
    Id.Map.t

val match_notation_constr : print_parentheses:bool ->
  factorize_eqns:PrintingFlags.Extern.FactorizeEqns.t ->
  'a glob_constr_g -> vars:Id.Set.t -> interpretation ->
  'a glob_constr_notation_substitution

(** Instances of notation variables, with their type as interpreted in
    a pattern *)
type 'a glob_cases_pattern_notation_substitution =
  ('a glob_constr_g, 'a cases_pattern_g, unit) notation_arg_type
    Id.Map.t

(** In a result [subst,(b,n,more_args)] of [match_notation_constr_cases_pattern]
    or [match_notation_constr_ind_pattern], [b] tells when the notation
    is a notation for a pattern of the form [@f] in which case implicit
    arguments are deactivated by convention. Otherwise, [n] tells how many
    arguments are involved in the notation and [more_args] are the
    extra arguments in case the pattern is a partially apply
    constructor. For instance, if the pattern is [C ?x ?y] with
    notation, say, "{x,y}" and the term is [C t1 t2 t3 t4], then [n]
    is [2] and [more_args] is [t3;t4] (the information is needed so
    that, later on, if e.g. [C] has its 3rd argument implicit, the
    term should be written "{x,y} t4" *)

val match_notation_constr_cases_pattern :
  'a cases_pattern_g -> interpretation ->
  'a glob_cases_pattern_notation_substitution * (bool * int * 'a cases_pattern_g list)

val match_notation_constr_ind_pattern :
  inductive -> 'a cases_pattern_g list -> interpretation ->
  'a glob_cases_pattern_notation_substitution * (bool * int * 'a cases_pattern_g list)
