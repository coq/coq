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
open Glob_term

(** [notation_constr] *)

(** [notation_constr] is the subtype of [glob_constr] allowed in syntactic
    extensions (i.e. notations).
    No location since intended to be substituted at any place of a text.
    Complex expressions such as fixpoints and cofixpoints are excluded,
    as well as non global expressions such as existential variables. *)

type notation_constr =
  (** Part common to [glob_constr] and [cases_pattern] *)
  | NRef of GlobRef.t
  | NVar of Id.t
  | NApp of notation_constr * notation_constr list
  | NHole of Evar_kinds.t * Namegen.intro_pattern_naming_expr * Genarg.glob_generic_argument option
  | NList of Id.t * Id.t * notation_constr * notation_constr * (* associativity: *) bool
  (** Part only in [glob_constr] *)
  | NLambda of Name.t * notation_constr * notation_constr
  | NProd of Name.t * notation_constr * notation_constr
  | NBinderList of Id.t * Id.t * notation_constr * notation_constr * (* associativity: *) bool
  | NLetIn of Name.t * notation_constr * notation_constr option * notation_constr
  | NCases of Constr.case_style * notation_constr option *
      (notation_constr * (Name.t * (inductive * Name.t list) option)) list *
      (cases_pattern list * notation_constr) list
  | NLetTuple of Name.t list * (Name.t * notation_constr option) *
      notation_constr * notation_constr
  | NIf of notation_constr * (Name.t * notation_constr option) *
      notation_constr * notation_constr
  | NRec of fix_kind * Id.t array *
      (Name.t * notation_constr option * notation_constr) list array *
      notation_constr array * notation_constr array
  | NSort of glob_sort
  | NCast of notation_constr * notation_constr cast_type

(** Note concerning NList: first constr is iterator, second is terminator;
    first id is where each argument of the list has to be substituted
    in iterator and snd id is alternative name just for printing;
    boolean is associativity *)

(** Types concerning notations *)

type scope_name = string

type tmp_scope_name = scope_name

type subscopes = tmp_scope_name option * scope_name list

type extended_subscopes = Constrexpr.notation_entry_level * subscopes

(** Type of the meta-variables of an notation_constr: in a recursive pattern x..y,
    x carries the sequence of objects bound to the list x..y  *)

type constr_as_binder_kind =
  | AsIdent
  | AsIdentOrPattern
  | AsStrictPattern

type notation_binder_source =
  (* This accepts only pattern *)
  (* NtnParsedAsPattern true means only strict pattern (no single variable) at printing *)
  | NtnParsedAsPattern of bool
  (* This accepts only ident *)
  | NtnParsedAsIdent
  (* This accepts ident, or pattern, or both *)
  | NtnBinderParsedAsConstr of constr_as_binder_kind

type notation_var_instance_type =
  | NtnTypeConstr | NtnTypeBinder of notation_binder_source | NtnTypeConstrList | NtnTypeBinderList

(** Type of variables when interpreting a constr_expr as a notation_constr:
    in a recursive pattern x..y, both x and y carry the individual type
    of each element of the list x..y *)
type notation_var_internalization_type =
  | NtnInternTypeAny | NtnInternTypeOnlyBinder

(** This characterizes to what a notation is interpreted to *)
type interpretation =
    (Id.t * (extended_subscopes * notation_var_instance_type)) list *
    notation_constr

type reversibility_status = APrioriReversible | HasLtac | NonInjective of Id.t list

type notation_interp_env = {
  ninterp_var_type : notation_var_internalization_type Id.Map.t;
  ninterp_rec_vars : Id.t Id.Map.t;
}
