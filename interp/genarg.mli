(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Names
open Term
open Libnames
open Globnames
open Glob_term
open Genredexpr
open Pattern
open Constrexpr
open Term
open Misctypes

(** FIXME: nothing to do there. *)
val loc_of_or_by_notation : ('a -> Loc.t) -> 'a or_by_notation -> Loc.t

(** In globalize tactics, we need to keep the initial [constr_expr] to recompute
   in the environment by the effective calls to Intro, Inversion, etc 
   The [constr_expr] field is [None] in TacDef though *)
type glob_constr_and_expr = glob_constr * constr_expr option

type open_constr_expr = unit * constr_expr
type open_glob_constr = unit * glob_constr_and_expr

type glob_constr_pattern_and_expr = glob_constr_and_expr * constr_pattern

(** The route of a generic argument, from parsing to evaluation.
In the following diagram, "object" can be tactic_expr, constr, tactic_arg, etc.

{% \begin{%}verbatim{% }%}
             parsing          in_raw                            out_raw
   char stream ---> raw_object ---> raw_object generic_argument -------+
                          encapsulation                          decaps|
                                                                       |
                                                                       V
                                                                   raw_object
                                                                       |
                                                         globalization |
                                                                       V
                                                                   glob_object
                                                                       |
                                                                encaps |
                                                               in_glob |
                                                                       V
                                                           glob_object generic_argument
                                                                       |
          out                          in                     out_glob |
  object <--- object generic_argument <--- object <--- glob_object <---+
    |   decaps                       encaps      interp           decaps
    |
    V
effective use
{% \end{%}verbatim{% }%}

To distinguish between the uninterpreted (raw), globalized and
interpreted worlds, we annotate the type [generic_argument] by a
phantom argument which is either [constr_expr], [glob_constr] or
[constr].

Transformation for each type :
{% \begin{%}verbatim{% }%}
tag                            raw open type            cooked closed type

BoolArgType                    bool                      bool
IntArgType                     int                       int
IntOrVarArgType                int or_var                int
StringArgType                  string (parsed w/ "")     string
PreIdentArgType                string (parsed w/o "")    (vernac only)
IdentArgType true              identifier                identifier
IdentArgType false             identifier (pattern_ident) identifier
IntroPatternArgType            intro_pattern_expr        intro_pattern_expr
VarArgType                     identifier located        identifier
RefArgType                     reference                 global_reference
QuantHypArgType                quantified_hypothesis     quantified_hypothesis
ConstrArgType                  constr_expr               constr
ConstrMayEvalArgType           constr_expr may_eval      constr
OpenConstrArgType              open_constr_expr          open_constr
ConstrWithBindingsArgType      constr_expr with_bindings constr with_bindings
BindingsArgType                constr_expr bindings      constr bindings
List0ArgType of argument_type
List1ArgType of argument_type
OptArgType of argument_type
ExtraArgType of string         '_a                      '_b
{% \end{%}verbatim{% }%}
*)

(** {5 Generic types} *)

type ('raw, 'glob, 'top) genarg_type
(** Generic types. ['raw] is the OCaml lowest level, ['glob] is the globalized
    one, and ['top] the internalized one. *)

type 'a uniform_genarg_type = ('a, 'a, 'a) genarg_type
(** Alias for concision when the three types agree. *)

val create_arg : 'raw option -> string -> ('raw, 'glob, 'top) genarg_type
(** Create a new generic type of argument: force to associate
   unique ML types at each of the three levels. FIXME: almost deprecated. *)

(** {5 Specialized types} *)

(** All of [rlevel], [glevel] and [tlevel] must be non convertible
   to ensure the injectivity of the type inference from type
   ['co generic_argument] to [('a,'co) abstract_argument_type];
   this guarantees that, for 'co fixed, the type of
   out_gen is monomorphic over 'a, hence type-safe
*)

type rlevel
type glevel
type tlevel

type ('a, 'co) abstract_argument_type
(** Type at level ['co] represented by an OCaml value of type ['a]. *)

type 'a raw_abstract_argument_type = ('a, rlevel) abstract_argument_type
(** Specialized type at raw level. *)

type 'a glob_abstract_argument_type = ('a, glevel) abstract_argument_type
(** Specialized type at globalized level. *)

type 'a typed_abstract_argument_type = ('a, tlevel) abstract_argument_type
(** Specialized type at internalized level. *)

(** {6 Projections} *)

val rawwit : ('a, 'b, 'c) genarg_type -> ('a, rlevel) abstract_argument_type
(** Projection on the raw type constructor. *)

val glbwit : ('a, 'b, 'c) genarg_type -> ('b, glevel) abstract_argument_type
(** Projection on the globalized type constructor. *)

val topwit : ('a, 'b, 'c) genarg_type -> ('c, tlevel) abstract_argument_type
(** Projection on the internalized type constructor. *)

(** {5 Generic arguments} *)

type 'a generic_argument
(** A inhabitant of ['level generic_argument] is a inhabitant of some type at
    level ['level], together with the representation of this type. *)

type raw_generic_argument = rlevel generic_argument
type glob_generic_argument = glevel generic_argument
type typed_generic_argument = tlevel generic_argument

(** {6 Constructors} *)

val in_gen : ('a, 'co) abstract_argument_type -> 'a -> 'co generic_argument
(** [in_gen t x] embeds an argument of type [t] into a generic argument. *)

val out_gen : ('a, 'co) abstract_argument_type -> 'co generic_argument -> 'a
(** [out_gen t x] recovers an argument of type [t] from a generic argument. It
    fails if [x] has not the right dynamic type. *)

val has_type : 'co generic_argument -> ('a, 'co) abstract_argument_type -> bool
(** [has_type v t] tells whether [v] has type [t]. If true, it ensures that
    [out_gen t v] will not raise a dynamic type exception. *)

(** {6 Manipulation of generic arguments}

Those functions fail if they are applied to an argument which has not the right
dynamic type. *)

val fold_list0 :
 ('a generic_argument -> 'c -> 'c) -> 'a generic_argument -> 'c -> 'c

val fold_list1 :
 ('a generic_argument -> 'c -> 'c) -> 'a generic_argument -> 'c -> 'c

val fold_opt :
 ('a generic_argument -> 'c) -> 'c -> 'a generic_argument -> 'c

val fold_pair :
 ('a generic_argument -> 'a generic_argument -> 'c) ->
      'a generic_argument -> 'c

(** [app_list0] fails if applied to an argument not of tag [List0 t]
    for some [t]; it's the responsability of the caller to ensure it *)

val app_list0 : ('a generic_argument -> 'b generic_argument) ->
'a generic_argument -> 'b generic_argument

val app_list1 : ('a generic_argument -> 'b generic_argument) ->
'a generic_argument -> 'b generic_argument

val app_opt : ('a generic_argument -> 'b generic_argument) ->
'a generic_argument -> 'b generic_argument

val app_pair :
  ('a generic_argument -> 'b generic_argument) ->
      ('a generic_argument -> 'b generic_argument)
   -> 'a generic_argument -> 'b generic_argument

(** {6 High-level creation} *)

(** {5 Genarg environments} *)

type glob_sign = {
  ltacvars : Id.t list * Id.t list;
  ltacrecvars : (Id.t * Nametab.ltac_constant) list;
  gsigma : Evd.evar_map;
  genv : Environ.env }

module TacStore : Store.S

type interp_sign = {
  lfun : (Id.t * tlevel generic_argument) list;
  extra : TacStore.t }

(** {5 Generic arguments} *)

type ('raw, 'glb, 'top) arg0 = {
  arg0_rprint : 'raw -> std_ppcmds;
  (** Printing at raw level function. *)
  arg0_gprint : 'glb -> std_ppcmds;
  (** Printing at glob level function. *)
  arg0_tprint : 'top -> std_ppcmds;
  (** Printing at top level function. *)
  arg0_glob : glob_sign -> 'raw -> glob_sign * 'glb;
  (** Globalization function. *)
  arg0_subst : Mod_subst.substitution -> 'glb -> 'glb;
  (** Substitution function. *)
  arg0_interp : interp_sign ->
    Goal.goal Evd.sigma -> 'glb -> Evd.evar_map * 'top;
  (** Intepretation function. *)
}

val make0 : 'raw option -> string -> ('raw, 'glb, 'top) arg0 ->
  ('raw, 'glb, 'top) genarg_type
(** [make0 def name arg] create a generic argument named [name] with the
    manipulation functions defined in [arg], and with a default empty value
    [def]. FIXME: [def] is related to parsing and should be put elsewhere. *)

val default_arg0 : string -> ('raw, 'glb, 'top) arg0
(** A default [arg0] with a given name. Printing functions print a dummy value
    and glob/subst/interp all fail. *)

val default_uniform_arg0 : string -> ('a, 'a, 'a) arg0
(** A default uniform [arg0] with a given name. Printing functions print a dummy
    value and glob/subst/interp are all identity. *)

val arg_gen : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb, 'top) arg0
(** Create the manipulation functions for any generic argument type. *)

(** {5 Generic manipulation functions}

  Those functions are the counterparts of [arg0] fields, but they apply on any
  generic argument.

  FIXME: only partially implemented for now. *)

val raw_print : rlevel generic_argument -> std_ppcmds
val glb_print : glevel generic_argument -> std_ppcmds
val top_print : tlevel generic_argument -> std_ppcmds

val globalize : glob_sign ->
  rlevel generic_argument -> glob_sign * glevel generic_argument

val substitute : Mod_subst.substitution ->
  glevel generic_argument -> glevel generic_argument

val interpret : interp_sign -> Goal.goal Evd.sigma ->
  glevel generic_argument -> Evd.evar_map * tlevel generic_argument

(** {6 Type reification} *)

type argument_type =
  (** Basic types *)
  | BoolArgType
  | IntArgType
  | IntOrVarArgType
  | StringArgType
  | PreIdentArgType
  | IntroPatternArgType
  | IdentArgType of bool
  | VarArgType
  | RefArgType
  (** Specific types *)
  | GenArgType
  | SortArgType
  | ConstrArgType
  | ConstrMayEvalArgType
  | QuantHypArgType
  | OpenConstrArgType of bool
  | ConstrWithBindingsArgType
  | BindingsArgType
  | RedExprArgType
  | List0ArgType of argument_type
  | List1ArgType of argument_type
  | OptArgType of argument_type
  | PairArgType of argument_type * argument_type
  | ExtraArgType of string

val argument_type_eq : argument_type -> argument_type -> bool

val genarg_tag : 'a generic_argument -> argument_type

val unquote : ('a, 'co) abstract_argument_type -> argument_type

(** {5 Basic generic type constructors} *)

(** {6 Ground types} *)

open Evd

val wit_bool : bool uniform_genarg_type

val wit_int : int uniform_genarg_type

val wit_int_or_var : int or_var uniform_genarg_type

val wit_string : string uniform_genarg_type

val wit_pre_ident : string uniform_genarg_type

val wit_intro_pattern : intro_pattern_expr located uniform_genarg_type

val wit_ident : Id.t uniform_genarg_type

val wit_pattern_ident : Id.t uniform_genarg_type

val wit_ident_gen : bool -> Id.t uniform_genarg_type

val wit_var : (Id.t located, Id.t located, Id.t) genarg_type

val wit_ref : (reference, global_reference located or_var, global_reference) genarg_type

val wit_quant_hyp : quantified_hypothesis uniform_genarg_type

val wit_genarg : (raw_generic_argument, glob_generic_argument, typed_generic_argument) genarg_type

val wit_sort : (glob_sort, glob_sort, sorts) genarg_type

val wit_constr : (constr_expr, glob_constr_and_expr, constr) genarg_type

val wit_constr_may_eval :
  ((constr_expr,reference or_by_notation,constr_expr) may_eval,
  (glob_constr_and_expr,evaluable_global_reference and_short_name or_var,glob_constr_pattern_and_expr) may_eval,
  constr) genarg_type

val wit_open_constr_gen : bool -> (open_constr_expr, open_glob_constr, open_constr) genarg_type

val wit_open_constr : (open_constr_expr, open_glob_constr, open_constr) genarg_type

val wit_casted_open_constr : (open_constr_expr, open_glob_constr, open_constr) genarg_type

val wit_constr_with_bindings :
  (constr_expr with_bindings,
  glob_constr_and_expr with_bindings,
  constr with_bindings sigma) genarg_type

val wit_bindings :
  (constr_expr bindings,
  glob_constr_and_expr bindings,
  constr bindings sigma) genarg_type

val wit_red_expr :
  ((constr_expr,reference or_by_notation,constr_expr) red_expr_gen,
  (glob_constr_and_expr,evaluable_global_reference and_short_name or_var,glob_constr_pattern_and_expr) red_expr_gen,
  (constr,evaluable_global_reference,constr_pattern) red_expr_gen) genarg_type

(** {6 Parameterized types} *)

val wit_list0 : ('a, 'b, 'c) genarg_type -> ('a list, 'b list, 'c list) genarg_type
val wit_list1 : ('a, 'b, 'c) genarg_type -> ('a list, 'b list, 'c list) genarg_type
val wit_opt : ('a, 'b, 'c) genarg_type -> ('a option, 'b option, 'c option) genarg_type
val wit_pair : ('a1, 'b1, 'c1) genarg_type -> ('a2, 'b2, 'c2) genarg_type ->
  ('a1 * 'a2, 'b1 * 'b2, 'c1 * 'c2) genarg_type

(** {5 Magic used by the parser} *)

(** [in_generic] is used in combination with camlp4 [Gramext.action] magic

   [in_generic: !l:type, !a:argument_type -> |a|_l -> 'l generic_argument]

   where |a|_l is the interpretation of a at level l

   [in_generic] is not typable; we replace the second argument by an absurd
   type (with no introduction rule)
*)
type an_arg_of_this_type

val in_generic :
  argument_type -> an_arg_of_this_type -> 'co generic_argument

val default_empty_value : ('raw, 'glb, 'top) genarg_type -> 'raw option
