(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** Basic types used both in [constr_expr] and in [glob_constr] *)

(** Cases pattern variables *)

type patvar = Id.t

(** Introduction patterns *)

type 'constr intro_pattern_expr =
  | IntroForthcoming of bool
  | IntroNaming of intro_pattern_naming_expr
  | IntroAction of 'constr intro_pattern_action_expr
and intro_pattern_naming_expr =
  | IntroIdentifier of Id.t
  | IntroFresh of Id.t
  | IntroAnonymous
and 'constr intro_pattern_action_expr =
  | IntroWildcard
  | IntroOrAndPattern of 'constr or_and_intro_pattern_expr
  | IntroInjection of (Loc.t * 'constr intro_pattern_expr) list
  | IntroApplyOn of 'constr * (Loc.t * 'constr intro_pattern_expr)
  | IntroRewrite of bool
and 'constr or_and_intro_pattern_expr =
  (Loc.t * 'constr intro_pattern_expr) list list

(** Move destination for hypothesis *)

type 'id move_location =
  | MoveAfter of 'id
  | MoveBefore of 'id
  | MoveFirst
  | MoveLast (** can be seen as "no move" when doing intro *)

(** Sorts *)

type 'a glob_sort_gen = GProp | GSet | GType of 'a
type sort_info = string list
type level_info = string option

type glob_sort = sort_info glob_sort_gen
type glob_level = level_info glob_sort_gen

(** A synonym of [Evar.t], also defined in Term *)

type existential_key = Evar.t

(** Case style, shared with Term *)

type case_style = Term.case_style =
  | LetStyle
  | IfStyle
  | LetPatternStyle
  | MatchStyle
  | RegularStyle (** infer printing form from number of constructor *)

(** Casts *)

type 'a cast_type =
  | CastConv of 'a
  | CastVM of 'a
  | CastCoerce (** Cast to a base type (eg, an underlying inductive type) *)
  | CastNative of 'a

(** Bindings *)

type quantified_hypothesis = AnonHyp of int | NamedHyp of Id.t

type 'a explicit_bindings = (Loc.t * quantified_hypothesis * 'a) list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings


(** Some utility types for parsing *)

type 'a or_var =
  | ArgArg of 'a
  | ArgVar of Names.Id.t Loc.located

type 'a and_short_name = 'a * Id.t Loc.located option

type 'a or_by_notation =
  | AN of 'a
  | ByNotation of (Loc.t * string * string option)

(* NB: the last string in [ByNotation] is actually a [Notation.delimiters],
   but this formulation avoids a useless dependency. *)


(** Kinds of modules *)

type module_kind = Module | ModType | ModAny
