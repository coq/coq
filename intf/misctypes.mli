(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames

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
and or_and_intro_pattern_expr = (Pp.loc * intro_pattern_expr) list list


(** Sorts *)

type glob_sort = GProp | GSet | GType of Univ.universe option

(** Casts *)

type 'a cast_type =
  | CastConv of 'a
  | CastVM of 'a
  | CastCoerce (** Cast to a base type (eg, an underlying inductive type) *)


(** Bindings *)

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_bindings = (Pp.loc * quantified_hypothesis * 'a) list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings


(** Some utility types for parsing *)

type 'a or_var =
  | ArgArg of 'a
  | ArgVar of Names.identifier Pp.located

type 'a and_short_name = 'a * identifier Pp.located option

type 'a or_by_notation =
  | AN of 'a
  | ByNotation of (Pp.loc * string * string option)

(* NB: the last string in [ByNotation] is actually a [Notation.delimiters],
   but this formulation avoids a useless dependency. *)
