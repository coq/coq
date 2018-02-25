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

(** Basic types used both in [constr_expr], [glob_constr], and [vernacexpr] *)

(** Located identifiers and objects with syntax. *)

type lident = Id.t CAst.t
type lname = Name.t CAst.t
type lstring = string CAst.t

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
  | IntroInjection of ('constr intro_pattern_expr) CAst.t list
  | IntroApplyOn of 'constr CAst.t * 'constr intro_pattern_expr CAst.t
  | IntroRewrite of bool
and 'constr or_and_intro_pattern_expr =
  | IntroOrPattern of ('constr intro_pattern_expr) CAst.t list list
  | IntroAndPattern of ('constr intro_pattern_expr) CAst.t list

(** Move destination for hypothesis *)

type 'id move_location =
  | MoveAfter of 'id
  | MoveBefore of 'id
  | MoveFirst
  | MoveLast (** can be seen as "no move" when doing intro *)

(** Sorts *)

type 'a glob_sort_gen =
  | GProp (** representation of [Prop] literal *)
  | GSet  (** representation of [Set] literal *)
  | GType of 'a (** representation of [Type] literal *)

type 'a universe_kind =
  | UAnonymous
  | UUnknown
  | UNamed of 'a

type level_info = Libnames.reference universe_kind
type glob_level = level_info glob_sort_gen
type glob_constraint = glob_level * Univ.constraint_type * glob_level

type sort_info = (Libnames.reference * int) option list
type glob_sort = sort_info glob_sort_gen

(** A synonym of [Evar.t], also defined in Term *)

type existential_key = Evar.t

(** Case style, shared with Term *)

type case_style = Constr.case_style =
  | LetStyle
  | IfStyle
  | LetPatternStyle
  | MatchStyle
  | RegularStyle (** infer printing form from number of constructor *)
[@@ocaml.deprecated "Alias for Constr.case_style"]

(** Casts *)

type 'a cast_type =
  | CastConv of 'a
  | CastVM of 'a
  | CastCoerce (** Cast to a base type (eg, an underlying inductive type) *)
  | CastNative of 'a

(** Bindings *)

type quantified_hypothesis = AnonHyp of int | NamedHyp of Id.t

type 'a explicit_bindings = (quantified_hypothesis * 'a) CAst.t list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings


(** Some utility types for parsing *)

type 'a or_var =
  | ArgArg of 'a
  | ArgVar of lident

type 'a and_short_name = 'a * lident option

type 'a or_by_notation_r =
  | AN of 'a
  | ByNotation of (string * string option)

type 'a or_by_notation = 'a or_by_notation_r CAst.t

(* NB: the last string in [ByNotation] is actually a [Notation.delimiters],
   but this formulation avoids a useless dependency. *)


(** Kinds of modules *)

type module_kind = Module | ModType | ModAny

(** Various flags *)

type direction_flag = bool (* true = Left-to-right    false = right-to-right *)
type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type letin_flag = bool     (* true = use local def    false = use Leibniz *)
type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)

type multi =
  | Precisely of int
  | UpTo of int
  | RepeatStar
  | RepeatPlus

type 'a core_destruction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of lident
  | ElimOnAnonHyp of int

type 'a destruction_arg =
  clear_flag * 'a core_destruction_arg

type inversion_kind =
  | SimpleInversion
  | FullInversion
  | FullInversionClear

type ('a, 'b) gen_universe_decl = {
  univdecl_instance : 'a; (* Declared universes *)
  univdecl_extensible_instance : bool; (* Can new universes be added *)
  univdecl_constraints : 'b; (* Declared constraints *)
  univdecl_extensible_constraints : bool (* Can new constraints be added *) }
