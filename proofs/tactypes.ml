(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Tactic-related types that are not totally Ltac specific and still used in
    lower API. It's not clear whether this is a temporary API or if this is
    meant to stay. *)

open Names

(** Introduction patterns *)

type 'constr intro_pattern_expr =
  | IntroForthcoming of bool
  | IntroNaming of Namegen.intro_pattern_naming_expr
  | IntroAction of 'constr intro_pattern_action_expr
and 'constr intro_pattern_action_expr =
  | IntroWildcard
  | IntroOrAndPattern of 'constr or_and_intro_pattern_expr
  | IntroInjection of ('constr intro_pattern_expr) CAst.t list
  | IntroApplyOn of 'constr CAst.t * 'constr intro_pattern_expr CAst.t
  | IntroRewrite of bool
and 'constr or_and_intro_pattern_expr =
  | IntroOrPattern of ('constr intro_pattern_expr) CAst.t list list
  | IntroAndPattern of ('constr intro_pattern_expr) CAst.t list

(** Bindings *)

type quantified_hypothesis = AnonHyp of int | NamedHyp of Id.t

type 'a explicit_bindings = (quantified_hypothesis * 'a) CAst.t list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings

type 'a delayed_open = Environ.env -> Evd.evar_map -> Evd.evar_map * 'a

type delayed_open_constr = EConstr.constr delayed_open
type delayed_open_constr_with_bindings = EConstr.constr with_bindings delayed_open

type intro_pattern = delayed_open_constr intro_pattern_expr CAst.t
type intro_patterns = delayed_open_constr intro_pattern_expr CAst.t list
type or_and_intro_pattern = delayed_open_constr or_and_intro_pattern_expr CAst.t
type intro_pattern_naming = Namegen.intro_pattern_naming_expr CAst.t
