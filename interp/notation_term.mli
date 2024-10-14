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
open Glob_term

(** [notation_constr] *)

(** [notation_constr] is the subtype of [glob_constr] allowed in syntactic
    extensions (i.e. notations).
    No location since intended to be substituted at any place of a text.
    Complex expressions such as fixpoints and cofixpoints are excluded,
    as well as non global expressions such as existential variables. *)

type notation_constr =
  (* Part common to [glob_constr] and [cases_pattern] *)
  | NRef of GlobRef.t * glob_instance option
  | NVar of Id.t
  | NApp of notation_constr * notation_constr list
  | NProj of (Constant.t * glob_instance option) * notation_constr list * notation_constr
  | NHole of glob_evar_kind
  | NGenarg of Genarg.glob_generic_argument
  | NList of Id.t * Id.t * notation_constr * notation_constr * (* associativity: *) bool
  (* Part only in [glob_constr] *)
  | NLambda of Name.t * notation_constr option * notation_constr
  | NProd of Name.t * notation_constr option * notation_constr
  | NBinderList of Id.t * Id.t * notation_constr * notation_constr * (* associativity: *) bool
  | NLetIn of Name.t * notation_constr * notation_constr option * notation_constr
  | NCases of Constr.case_style * notation_constr option *
      (notation_constr * (Name.t * (inductive * Name.t list) option)) list *
      (cases_pattern list * notation_constr) list
  | NLetTuple of Name.t list * (Name.t * notation_constr option) *
      notation_constr * notation_constr
  | NIf of notation_constr * (Name.t * notation_constr option) *
      notation_constr * notation_constr
  | NRec of glob_fix_kind * Id.t array *
      (Name.t * notation_constr option * notation_constr) list array *
      notation_constr array * notation_constr array
  | NSort of glob_sort
  | NCast of notation_constr * Constr.cast_kind option * notation_constr
  | NInt of Uint63.t
  | NFloat of Float64.t
  | NString of Pstring.t
  | NArray of notation_constr array * notation_constr * notation_constr

(** Note concerning NList: first constr is iterator, second is terminator;
    first id is where each argument of the list has to be substituted
    in iterator and snd id is alternative name just for printing;
    boolean is associativity *)

(** Types concerning notations *)

type scope_name = string

type tmp_scope_name = scope_name

type subscopes = tmp_scope_name list * scope_name list

type extended_subscopes = Constrexpr.notation_entry_relative_level * subscopes

(** Type of the meta-variables of an notation_constr: in a recursive pattern x..y,
    x carries the sequence of objects bound to the list x..y  *)

type notation_binder_kind =
  (* This accepts only ident *)
  | AsIdent
  (* This accepts only name *)
  | AsName
  (* This accepts pattern *)
  | AsAnyPattern
  (* This accepts only strict pattern (i.e. no single variable) at printing *)
  | AsStrictPattern

type notation_binder_source =
  (* Parsed as constr and constrained to be ident, name or pattern, depending on kind *)
  | NtnBinderParsedAsConstr of notation_binder_kind
  (* Parsed and interpreted as ident, name or pattern, depending on kind *)
  | NtnBinderParsedAsSomeBinderKind of notation_binder_kind
  (* Parsed as open or closed binder: This accepts ident, _, quoted pattern, etc. *)
  | NtnBinderParsedAsBinder

type notation_var_instance_type =
  | NtnTypeConstr
  | NtnTypeConstrList
  | NtnTypeBinder of notation_binder_source
  | NtnTypeBinderList of notation_binder_source

(** Type of variables when interpreting a constr_expr as a notation_constr:
    in a recursive pattern x..y, both x and y carry the individual type
    of each element of the list x..y *)
type notation_var_internalization_type =
  | NtnInternTypeAny of scope_name option
  | NtnInternTypeOnlyBinder

(** The set of other notation variables that are bound to a binder or
    binder list and that bind the given notation variable, for
    instance, in ["{ x | P }" := (sigT (fun x => P)], "x" is under an
    empty set of binders and "P" is under the binders bound to "x",
    that is, its notation_var_binders set is "x" *)
type notation_var_binders = Id.Set.t

(** This characterizes to what a notation is interpreted to *)
type interpretation =
    (Id.t * (extended_subscopes * notation_var_binders * notation_var_instance_type)) list *
    notation_constr

type forgetfulness = { forget_ltac : bool; forget_volatile_cast : bool }

type reversibility_status =
  | APrioriReversible
  | Forgetful of forgetfulness
  | NonInjective of Id.t list

type notation_interp_env = {
  ninterp_var_type : notation_var_internalization_type Id.Map.t;
  ninterp_rec_vars : Id.t Id.Map.t;
}
