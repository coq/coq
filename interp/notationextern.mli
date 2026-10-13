(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Declaration of uninterpretation functions (i.e. printing rules)
    for notations *)

open Names
open Constrexpr
open Glob_term
open Notation_term

val subscopes_eq : subscopes -> subscopes -> bool

val notation_entry_eq : notation_entry -> notation_entry -> bool
(** Equality on [notation_entry]. *)

val notation_entry_compare : notation_entry -> notation_entry -> int

val notation_with_optional_scope_eq : notation_with_optional_scope -> notation_with_optional_scope -> bool

val notation_eq : notation -> notation -> bool
(** Equality on [notation]. *)

val notation_compare : notation -> notation -> int

val specific_notation_compare : specific_notation -> specific_notation -> int

val notation_binder_kind_eq : notation_binder_kind -> notation_binder_kind -> bool
(** Equality on [notation_binder_kind]. *)

val interpretation_eq : interpretation -> interpretation -> bool
(** Equality on [interpretation]. *)

val notation_entry_level_eq : notation_entry_level -> notation_entry_level -> bool
(** Equality on [notation_entry_level]. *)

val notation_entry_relative_level_eq : notation_entry_relative_level -> notation_entry_relative_level -> bool
(** Equality on [notation_entry_relative_level]. *)

val subscopes_mk_tmp : scope_name list -> subscopes

val subscopes_unbounded : subscopes -> subscopes

type level = notation_entry_level * entry_relative_level list
(** The "signature" of a rule: its level together with the levels of its subentries *)

val level_eq : level -> level -> bool
(** Equality on [level]. *)

val entry_relative_level_eq : entry_relative_level -> entry_relative_level -> bool
(** Equality on [entry_relative_level]. *)

(** Binds a notation in a given scope to an interpretation *)
type interp_rule =
  | NotationRule of Constrexpr.specific_notation
  | AbbrevRule of Globnames.abbreviation

val remove_uninterpretation : Environ.env -> interp_rule -> interpretation -> unit
val declare_uninterpretation : Environ.env -> interp_rule -> interpretation -> unit

type notation_applicative_status =
  | AppBoundedNotation of int
  | AppUnboundedNotation
  | NotAppNotation

type notation_rule = {
  not_rule : interp_rule;
  not_patt : interpretation;
  not_status : notation_applicative_status;
}

(** Return the possible notations for a given term *)
val uninterp_notations : Environ.env -> 'a glob_constr_g -> notation_rule list
val uninterp_cases_pattern_notations : Environ.env -> 'a cases_pattern_g -> notation_rule list
val uninterp_ind_pattern_notations : Environ.env -> inductive -> notation_rule list

(** State protection *)
val with_notation_uninterpretation_protection : ('a -> 'b) -> 'a -> 'b

(** Miscellaneous *)
type notation_use =
  | OnlyPrinting
  | OnlyParsing
  | ParsingAndPrinting
