(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** Basic types used both in [constr_expr] and in [glob_constr] *)

(** Cases pattern variables *)

type patvar = identifier

(** Introduction patterns *)

type intro_pattern_expr =
  | IntroOrAndPattern of or_and_intro_pattern_expr
  | IntroWildcard
  | IntroRewrite of bool
  | IntroIdentifier of identifier
  | IntroFresh of identifier
  | IntroForthcoming of bool
  | IntroAnonymous
and or_and_intro_pattern_expr = (Loc.t * intro_pattern_expr) list list

(** Move destination for hypothesis *)

type 'id move_location =
  | MoveAfter of 'id
  | MoveBefore of 'id
  | MoveFirst
  | MoveLast (** can be seen as "no move" when doing intro *)

(** Sorts *)

type sort_info = string option
type glob_sort = GProp | GSet | GType of sort_info

(** A synonym of [int], also defined in Term *)

type existential_key = int

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

(** Bindings *)

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_bindings = (Loc.t * quantified_hypothesis * 'a) list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings


(** Some utility types for parsing *)

type 'a or_var =
  | ArgArg of 'a
  | ArgVar of Names.identifier Loc.located

type 'a and_short_name = 'a * identifier Loc.located option

type 'a or_by_notation =
  | AN of 'a
  | ByNotation of (Loc.t * string * string option)

(* NB: the last string in [ByNotation] is actually a [Notation.delimiters],
   but this formulation avoids a useless dependency. *)
