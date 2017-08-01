(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Loc
open Names
open Tac2expr

(** Quoted variants of Ltac syntactic categories. Contrarily to the former, they
    sometimes allow anti-quotations. Used for notation scopes. *)

type 'a or_anti =
| QExpr of 'a
| QAnti of Id.t located

type bindings =
| QImplicitBindings of raw_tacexpr list
| QExplicitBindings of (Misctypes.quantified_hypothesis or_anti * raw_tacexpr) Loc.located list
| QNoBindings

type intro_pattern =
| QIntroForthcoming of bool
| QIntroNaming of intro_pattern_naming
| QIntroAction of intro_pattern_action
and intro_pattern_naming =
| QIntroIdentifier of Id.t or_anti
| QIntroFresh of Id.t or_anti
| QIntroAnonymous
and intro_pattern_action =
| QIntroWildcard
| QIntroOrAndPattern of or_and_intro_pattern
| QIntroInjection of intro_pattern list
(* | QIntroApplyOn of Empty.t (** Not implemented yet *) *)
| QIntroRewrite of bool
and or_and_intro_pattern =
| QIntroOrPattern of intro_pattern list list
| QIntroAndPattern of intro_pattern list
