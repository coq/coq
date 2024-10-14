(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constrexpr

(** {6 Pretty-print. } *)

type ppbox =
  | PpHB
  | PpHOVB of int
  | PpHVB of int
  | PpVB of int

type ppcut =
  | PpBrk of int * int
  | PpFnl

val ppcmd_of_box : ppbox -> Pp.t -> Pp.t

val ppcmd_of_cut : ppcut -> Pp.t

(** {6 Printing rules for notations} *)

type pattern_quote_style = QuotedPattern | NotQuotedPattern

(** Declare and look for the printing rule for symbolic notations *)
type unparsing =
  | UnpMetaVar of notation_entry_relative_level
  | UnpBinderMetaVar of notation_entry_relative_level * pattern_quote_style
  | UnpListMetaVar of notation_entry_relative_level * unparsing list
  | UnpBinderListMetaVar of
      bool (* true if open binder *) *
      bool (* true if printed with a quote *) *
      unparsing list
  | UnpTerminal of string
  | UnpBox of ppbox * unparsing Loc.located list
  | UnpCut of ppcut

type unparsing_rule = unparsing list

val unparsing_eq : unparsing -> unparsing -> bool

type notation_printing_rules = {
  notation_printing_unparsing : unparsing_rule;
  notation_printing_level : entry_level;
}

type generic_notation_printing_rules = {
  notation_printing_reserved : bool;
  notation_printing_rules : notation_printing_rules;
}

val declare_generic_notation_printing_rules : notation -> generic_notation_printing_rules -> unit
val declare_specific_notation_printing_rules : specific_notation -> notation_printing_rules -> unit
val has_generic_notation_printing_rule : notation -> bool
val find_generic_notation_printing_rule : notation -> generic_notation_printing_rules
val find_specific_notation_printing_rule : specific_notation -> notation_printing_rules
val find_notation_printing_rule : notation_with_optional_scope option -> notation -> notation_printing_rules
