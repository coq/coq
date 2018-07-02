(* Compat module, to be removed in 8.10 *)
open Names

type lident = Names.lident
[@@ocaml.deprecated "use [Names.lident"]
type lname = Names.lname
[@@ocaml.deprecated "use [Names.lname]"]
type lstring = Names.lstring
[@@ocaml.deprecated "use [Names.lstring]"]

type 'a or_by_notation_r = 'a Constrexpr.or_by_notation_r =
  | AN of 'a [@ocaml.deprecated "use version in [Constrexpr]"]
  | ByNotation of (string * string option) [@ocaml.deprecated "use version in [Constrexpr]"]
[@@ocaml.deprecated "use [Constrexpr.or_by_notation_r]"]

type 'a or_by_notation = 'a Constrexpr.or_by_notation
[@@ocaml.deprecated "use [Constrexpr.or_by_notation]"]

type intro_pattern_naming_expr = Namegen.intro_pattern_naming_expr =
  | IntroIdentifier of Id.t [@ocaml.deprecated "Use version in [Namegen]"]
  | IntroFresh of Id.t [@ocaml.deprecated "Use version in [Namegen]"]
  | IntroAnonymous [@ocaml.deprecated "Use version in [Namegen]"]
[@@ocaml.deprecated "use [Namegen.intro_pattern_naming_expr]"]

type 'a or_var = 'a Locus.or_var =
  | ArgArg of 'a [@ocaml.deprecated "Use version in [Locus]"]
  | ArgVar of Names.lident [@ocaml.deprecated "Use version in [Locus]"]
[@@ocaml.deprecated "use [Locus.or_var]"]

type quantified_hypothesis = Tactypes.quantified_hypothesis =
    AnonHyp of int [@ocaml.deprecated "Use version in [Tactypes]"]
  | NamedHyp of Id.t [@ocaml.deprecated "Use version in [Tactypes]"]
[@@ocaml.deprecated "use [Tactypes.quantified_hypothesis]"]

type multi = Equality.multi =
  | Precisely of int [@ocaml.deprecated "use version in [Equality]"]
  | UpTo of int [@ocaml.deprecated "use version in [Equality]"]
  | RepeatStar [@ocaml.deprecated "use version in [Equality]"]
  | RepeatPlus [@ocaml.deprecated "use version in [Equality]"]
[@@ocaml.deprecated "use [Equality.multi]"]

type 'a bindings = 'a Tactypes.bindings =
  | ImplicitBindings of 'a list [@ocaml.deprecated "use version in [Tactypes]"]
  | ExplicitBindings of 'a Tactypes.explicit_bindings [@ocaml.deprecated "use version in [Tactypes]"]
  | NoBindings [@ocaml.deprecated "use version in [Tactypes]"]
[@@ocaml.deprecated "use [Tactypes.bindings]"]

type 'constr intro_pattern_expr = 'constr Tactypes.intro_pattern_expr =
  | IntroForthcoming of bool [@ocaml.deprecated "use version in [Tactypes]"]
  | IntroNaming of Namegen.intro_pattern_naming_expr [@ocaml.deprecated "use version in [Tactypes]"]
  | IntroAction of 'constr Tactypes.intro_pattern_action_expr [@ocaml.deprecated "use version in [Tactypes]"]
and 'constr intro_pattern_action_expr = 'constr Tactypes.intro_pattern_action_expr =
  | IntroWildcard [@ocaml.deprecated "use [Tactypes]"]
  | IntroOrAndPattern of 'constr Tactypes.or_and_intro_pattern_expr [@ocaml.deprecated "use [Tactypes]"]
  | IntroInjection of ('constr intro_pattern_expr) CAst.t list [@ocaml.deprecated "use [Tactypes]"]
  | IntroApplyOn of 'constr CAst.t * 'constr intro_pattern_expr CAst.t [@ocaml.deprecated "use [Tactypes]"]
  | IntroRewrite of bool [@ocaml.deprecated "use [Tactypes]"]
and 'constr or_and_intro_pattern_expr = 'constr Tactypes.or_and_intro_pattern_expr =
  | IntroOrPattern of ('constr intro_pattern_expr) CAst.t list list [@ocaml.deprecated "use [Tactypes]"]
  | IntroAndPattern of ('constr intro_pattern_expr) CAst.t list [@ocaml.deprecated "use [Tactypes]"]
[@@ocaml.deprecated "use version in [Tactypes]"]

type 'id move_location = 'id Logic.move_location =
  | MoveAfter of 'id [@ocaml.deprecated "use version in [Logic]"]
  | MoveBefore of 'id [@ocaml.deprecated "use version in [Logic]"]
  | MoveFirst [@ocaml.deprecated "use version in [Logic]"]
  | MoveLast [@ocaml.deprecated "use version in [Logic]"]
[@@ocaml.deprecated "use version in [Logic]"]

type 'a cast_type = 'a Glob_term.cast_type =
  | CastConv of 'a [@ocaml.deprecated "use version in [Glob_term]"]
  | CastVM of 'a [@ocaml.deprecated "use version in [Glob_term]"]
  | CastCoerce [@ocaml.deprecated "use version in [Glob_term]"]
  | CastNative of 'a [@ocaml.deprecated "use version in [Glob_term]"]
[@@ocaml.deprecated "use version in [Glob_term]"]
