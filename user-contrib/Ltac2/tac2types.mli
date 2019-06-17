(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Proofview

(** Redefinition of Ltac1 data structures because of impedance mismatch *)

type evars_flag = bool
type advanced_flag = bool

type 'a thunk = (unit, 'a) Tac2ffi.fun1

type quantified_hypothesis = Tactypes.quantified_hypothesis =
| AnonHyp of int
| NamedHyp of Id.t

type explicit_bindings = (quantified_hypothesis * EConstr.t) list

type bindings =
| ImplicitBindings of EConstr.t list
| ExplicitBindings of explicit_bindings
| NoBindings

type constr_with_bindings = EConstr.constr * bindings

type core_destruction_arg =
| ElimOnConstr of constr_with_bindings tactic
| ElimOnIdent of Id.t
| ElimOnAnonHyp of int

type destruction_arg = core_destruction_arg

type intro_pattern =
| IntroForthcoming of bool
| IntroNaming of intro_pattern_naming
| IntroAction of intro_pattern_action
and intro_pattern_naming =
| IntroIdentifier of Id.t
| IntroFresh of Id.t
| IntroAnonymous
and intro_pattern_action =
| IntroWildcard
| IntroOrAndPattern of or_and_intro_pattern
| IntroInjection of intro_pattern list
| IntroApplyOn of EConstr.t thunk * intro_pattern
| IntroRewrite of bool
and or_and_intro_pattern =
| IntroOrPattern of intro_pattern list list
| IntroAndPattern of intro_pattern list

type occurrences =
| AllOccurrences
| AllOccurrencesBut of int list
| NoOccurrences
| OnlyOccurrences of int list

type hyp_location_flag = Locus.hyp_location_flag =
| InHyp | InHypTypeOnly | InHypValueOnly

type hyp_location = Id.t * occurrences * hyp_location_flag

type clause =
  { onhyps : hyp_location list option;
    concl_occs : occurrences }

type induction_clause =
  destruction_arg *
  intro_pattern_naming option *
  or_and_intro_pattern option *
  clause option

type multi = Equality.multi =
| Precisely of int
| UpTo of int
| RepeatStar
| RepeatPlus

type rewriting =
  bool option *
  multi *
  constr_with_bindings tactic

type assertion =
| AssertType of intro_pattern option * constr * unit thunk option
| AssertValue of Id.t * constr
