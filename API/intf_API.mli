(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file should respect the dependency order established
   in Coq. To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done && echo -e "\n## highparsing files" && cat parsing/highparsing.mllib' > API/link
   ```

   Note however that files in intf/ are located manually now as their
   conceptual linking order in the Coq codebase is incorrect (but it
   works due to these files being implementation-free.

   See below in the file for their concrete position.
*)

open Kernel_API

(************************************************************************)
(* Modules from intf/                                                   *)
(************************************************************************)

module Misctypes :
sig
  type evars_flag = bool
  type clear_flag = bool option
  type advanced_flag = bool
  type rec_flag = bool

  type 'a or_by_notation =
    | AN of 'a
    | ByNotation of (string * string option) Loc.located

  type 'a or_var =
                 | ArgArg of 'a
                 | ArgVar of Names.Id.t Loc.located

  type 'a and_short_name = 'a * Names.Id.t Loc.located option

  type 'a glob_sort_gen =
    | GProp (** representation of [Prop] literal *)
    | GSet  (** representation of [Set] literal *)
    | GType of 'a (** representation of [Type] literal *)

  type level_info = Names.Name.t Loc.located option
  type glob_level = level_info glob_sort_gen

  type sort_info = Names.Name.t Loc.located list
  type glob_sort = sort_info glob_sort_gen

  type case_style = Term.case_style =
    | LetStyle
    | IfStyle
    | LetPatternStyle
    | MatchStyle
    | RegularStyle (** infer printing form from number of constructor *)

  type 'a cast_type =
                    | CastConv of 'a
                    | CastVM of 'a
                    | CastCoerce
                    | CastNative of 'a

  type 'constr intro_pattern_expr =
    | IntroForthcoming of bool
    | IntroNaming of intro_pattern_naming_expr
    | IntroAction of 'constr intro_pattern_action_expr
  and intro_pattern_naming_expr =
    | IntroIdentifier of Names.Id.t
    | IntroFresh of Names.Id.t
    | IntroAnonymous
  and 'constr intro_pattern_action_expr =
    | IntroWildcard
    | IntroOrAndPattern of 'constr or_and_intro_pattern_expr
    | IntroInjection of ('constr intro_pattern_expr) Loc.located list
    | IntroApplyOn of 'constr Loc.located * 'constr intro_pattern_expr Loc.located
    | IntroRewrite of bool
  and 'constr or_and_intro_pattern_expr =
    | IntroOrPattern of ('constr intro_pattern_expr) Loc.located list list
    | IntroAndPattern of ('constr intro_pattern_expr) Loc.located list

  type quantified_hypothesis =
    | AnonHyp of int
    | NamedHyp of Names.Id.t

  type 'a explicit_bindings = (quantified_hypothesis * 'a) Loc.located list

  type 'a bindings =
    | ImplicitBindings of 'a list
    | ExplicitBindings of 'a explicit_bindings
    | NoBindings

  type 'a with_bindings = 'a * 'a bindings

  type 'a core_destruction_arg =
    | ElimOnConstr of 'a
    | ElimOnIdent of Names.Id.t Loc.located
    | ElimOnAnonHyp of int

  type inversion_kind =
    | SimpleInversion
    | FullInversion
    | FullInversionClear

  type multi =
    | Precisely of int
    | UpTo of int
    | RepeatStar
    | RepeatPlus

  type 'id move_location =
    | MoveAfter of 'id
    | MoveBefore of 'id
    | MoveFirst
    | MoveLast

  type 'a destruction_arg = clear_flag * 'a core_destruction_arg

end

module Locus :
sig
  type 'a occurrences_gen =
  | AllOccurrences
  | AllOccurrencesBut of 'a list (** non-empty *)
  | NoOccurrences
  | OnlyOccurrences of 'a list (** non-empty *)
  type occurrences = int occurrences_gen
  type occurrences_expr = (int Misctypes.or_var) occurrences_gen
  type 'a with_occurrences = occurrences_expr * 'a
  type hyp_location_flag =
                             InHyp | InHypTypeOnly | InHypValueOnly
  type 'a hyp_location_expr = 'a with_occurrences * hyp_location_flag
  type 'id clause_expr =
  { onhyps : 'id hyp_location_expr list option;
    concl_occs : occurrences_expr }
  type clause = Names.Id.t clause_expr
  type hyp_location = Names.Id.t * hyp_location_flag
  type goal_location = hyp_location option
end

(************************************************************************)
(* End Modules from intf/                                               *)
(************************************************************************)
