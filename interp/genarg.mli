(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util
open Names
open Term
open Libnames
open Rawterm
open Topconstr
open Term

type 'a and_short_name = 'a * identifier located option

(* In globalize tactics, we need to keep the initial [constr_expr] to recompute*)
(* in the environment by the effective calls to Intro, Inversion, etc *)
(* The [constr_expr] field is [None] in TacDef though *)
type rawconstr_and_expr = rawconstr * constr_expr option

type open_constr = Evd.evar_map * Term.constr
type open_constr_expr = unit * constr_expr
type open_rawconstr = unit * rawconstr_and_expr

type intro_pattern_expr =
  | IntroOrAndPattern of case_intro_pattern_expr
  | IntroWildcard
  | IntroIdentifier of identifier
  | IntroAnonymous
and case_intro_pattern_expr = intro_pattern_expr list list

val pr_intro_pattern : intro_pattern_expr -> Pp.std_ppcmds
val pr_case_intro_pattern : case_intro_pattern_expr -> Pp.std_ppcmds

(* The route of a generic argument, from parsing to evaluation

\begin{verbatim}
              parsing        in_raw                           out_raw
    char stream ----> rawtype ----> rawconstr generic_argument ---->
                                                                   |
                                                                   | interp
                                                                   V
                          type  <---- constr generic_argument  <----
                                  out                            in
\end{verbatim}

To distinguish between the uninterpreted (raw) and the interpreted
worlds, we annotate the type [generic_argument] by a phantom argument
which is either [constr_expr] or [constr] (actually we add also a second
argument [raw_tactic_expr] and [tactic], but this is only for technical
reasons, because these types are undefined at the type of compilation
of [Genarg]).

Transformation for each type :
\begin{verbatim}
tag                            raw open type            cooked closed type

BoolArgType                    bool                     bool
IntArgType                     int                      int
IntOrVarArgType                int or_var               int
StringArgType                  string (parsed w/ "")    string
PreIdentArgType                string (parsed w/o "")   (vernac only)
IdentArgType                   identifier               identifier
IntroPatternArgType            intro_pattern_expr       intro_pattern_expr
VarArgType                     identifier               constr
RefArgType                     reference                global_reference
ConstrArgType                  constr_expr              constr
ConstrMayEvalArgType           constr_expr may_eval     constr
QuantHypArgType                quantified_hypothesis    quantified_hypothesis
OpenConstrArgType              constr_expr              open_constr
ConstrBindingsArgType      constr_expr with_bindings constr with_bindings
List0ArgType of argument_type
List1ArgType of argument_type
OptArgType of argument_type
ExtraArgType of string         '_a                      '_b
\end{verbatim}
*)

(* All of [rlevel], [glevel] and [tlevel] must be non convertible 
   to ensure the injectivity of the type inference from type
   [('co,'ta) generic_argument] to [('a,'co,'ta) abstract_argument_type]
   is injective; this guarantees that, for 'b fixed, the type of
   out_gen is monomorphic over 'a, hence type-safe 
*)

type rlevel = constr_expr
type glevel = rawconstr_and_expr
type tlevel = constr

type ('a,'co,'ta) abstract_argument_type

val rawwit_bool : (bool,rlevel,'ta) abstract_argument_type
val globwit_bool : (bool,glevel,'ta) abstract_argument_type
val wit_bool : (bool,tlevel,'ta) abstract_argument_type

val rawwit_int : (int,rlevel,'ta) abstract_argument_type
val globwit_int : (int,glevel,'ta) abstract_argument_type
val wit_int : (int,tlevel,'ta) abstract_argument_type

val rawwit_int_or_var : (int or_var,rlevel,'ta) abstract_argument_type
val globwit_int_or_var : (int or_var,glevel,'ta) abstract_argument_type
val wit_int_or_var : (int or_var,tlevel,'ta) abstract_argument_type

val rawwit_string : (string,rlevel,'ta) abstract_argument_type
val globwit_string : (string,glevel,'ta) abstract_argument_type
val wit_string : (string,tlevel,'ta) abstract_argument_type

val rawwit_pre_ident : (string,rlevel,'ta) abstract_argument_type
val globwit_pre_ident : (string,glevel,'ta) abstract_argument_type
val wit_pre_ident : (string,tlevel,'ta) abstract_argument_type

val rawwit_intro_pattern : (intro_pattern_expr,rlevel,'ta) abstract_argument_type
val globwit_intro_pattern : (intro_pattern_expr,glevel,'ta) abstract_argument_type
val wit_intro_pattern : (intro_pattern_expr,tlevel,'ta) abstract_argument_type

val rawwit_ident : (identifier,rlevel,'ta) abstract_argument_type
val globwit_ident : (identifier,glevel,'ta) abstract_argument_type
val wit_ident : (identifier,tlevel,'ta) abstract_argument_type

val rawwit_var : (identifier located,rlevel,'ta) abstract_argument_type
val globwit_var : (identifier located,glevel,'ta) abstract_argument_type
val wit_var : (identifier,tlevel,'ta) abstract_argument_type

val rawwit_ref : (reference,rlevel,'ta) abstract_argument_type
val globwit_ref : (global_reference located or_var,glevel,'ta) abstract_argument_type
val wit_ref : (global_reference,tlevel,'ta) abstract_argument_type

val rawwit_quant_hyp : (quantified_hypothesis,rlevel,'ta) abstract_argument_type
val globwit_quant_hyp : (quantified_hypothesis,glevel,'ta) abstract_argument_type
val wit_quant_hyp : (quantified_hypothesis,tlevel,'ta) abstract_argument_type

val rawwit_sort : (rawsort,rlevel,'ta) abstract_argument_type
val globwit_sort : (rawsort,glevel,'ta) abstract_argument_type
val wit_sort : (sorts,tlevel,'ta) abstract_argument_type

val rawwit_constr : (constr_expr,rlevel,'ta) abstract_argument_type
val globwit_constr : (rawconstr_and_expr,glevel,'ta) abstract_argument_type
val wit_constr : (constr,tlevel,'ta) abstract_argument_type

val rawwit_constr_may_eval : ((constr_expr,reference) may_eval,rlevel,'ta) abstract_argument_type
val globwit_constr_may_eval : ((rawconstr_and_expr,evaluable_global_reference and_short_name or_var) may_eval,glevel,'ta) abstract_argument_type
val wit_constr_may_eval : (constr,tlevel,'ta) abstract_argument_type

val rawwit_open_constr_gen : bool -> (open_constr_expr,rlevel,'ta) abstract_argument_type
val globwit_open_constr_gen : bool -> (open_rawconstr,glevel,'ta) abstract_argument_type
val wit_open_constr_gen : bool -> (open_constr,tlevel,'ta) abstract_argument_type

val rawwit_open_constr : (open_constr_expr,rlevel,'ta) abstract_argument_type
val globwit_open_constr : (open_rawconstr,glevel,'ta) abstract_argument_type
val wit_open_constr : (open_constr,tlevel,'ta) abstract_argument_type

val rawwit_casted_open_constr : (open_constr_expr,rlevel,'ta) abstract_argument_type
val globwit_casted_open_constr : (open_rawconstr,glevel,'ta) abstract_argument_type
val wit_casted_open_constr : (open_constr,tlevel,'ta) abstract_argument_type

val rawwit_constr_with_bindings : (constr_expr with_bindings,rlevel,'ta) abstract_argument_type
val globwit_constr_with_bindings : (rawconstr_and_expr with_bindings,glevel,'ta) abstract_argument_type
val wit_constr_with_bindings : (constr with_bindings,tlevel,'ta) abstract_argument_type

val rawwit_bindings : (constr_expr bindings,rlevel,'ta) abstract_argument_type
val globwit_bindings : (rawconstr_and_expr bindings,glevel,'ta) abstract_argument_type
val wit_bindings : (constr bindings,tlevel,'ta) abstract_argument_type

val rawwit_red_expr : ((constr_expr,reference) red_expr_gen,rlevel,'ta) abstract_argument_type
val globwit_red_expr : ((rawconstr_and_expr,evaluable_global_reference and_short_name or_var) red_expr_gen,glevel,'ta) abstract_argument_type
val wit_red_expr : ((constr,evaluable_global_reference) red_expr_gen,tlevel,'ta) abstract_argument_type

val wit_list0 :
  ('a,'co,'ta) abstract_argument_type -> ('a list,'co,'ta) abstract_argument_type

val wit_list1 :
  ('a,'co,'ta) abstract_argument_type -> ('a list,'co,'ta) abstract_argument_type

val wit_opt :
  ('a,'co,'ta) abstract_argument_type -> ('a option,'co,'ta) abstract_argument_type

val wit_pair :
  ('a,'co,'ta) abstract_argument_type ->
  ('b,'co,'ta) abstract_argument_type ->
      ('a * 'b,'co,'ta) abstract_argument_type

(* ['a generic_argument] = (Sigma t:type. t[[constr/'a]]) *)
type ('a,'b) generic_argument

val fold_list0 : 
 (('a,'b) generic_argument -> 'c -> 'c) -> ('a,'b) generic_argument -> 'c -> 'c

val fold_list1 : 
 (('a,'b) generic_argument -> 'c -> 'c) -> ('a,'b) generic_argument -> 'c -> 'c

val fold_opt :
 (('a,'b) generic_argument -> 'c) -> 'c -> ('a,'b) generic_argument -> 'c

val fold_pair :
 (('a,'b) generic_argument -> ('a,'b) generic_argument -> 'c) -> 
      ('a,'b) generic_argument -> 'c

(* [app_list0] fails if applied to an argument not of tag [List0 t]
    for some [t]; it's the responsability of the caller to ensure it *)

val app_list0 : (('a,'b) generic_argument -> ('c,'d) generic_argument) -> 
('a,'b) generic_argument -> ('c,'d) generic_argument

val app_list1 : (('a,'b) generic_argument -> ('c,'d) generic_argument) -> 
('a,'b) generic_argument -> ('c,'d) generic_argument

val app_opt : (('a,'b) generic_argument -> ('c,'d) generic_argument) -> 
('a,'b) generic_argument -> ('c,'d) generic_argument

val app_pair :
  (('a,'b) generic_argument -> ('c,'d) generic_argument) ->
      (('a,'b) generic_argument -> ('c,'d) generic_argument)
   -> ('a,'b) generic_argument -> ('c,'d) generic_argument

(* Manque l'ordre supérieur, on aimerait ('co,'ta) 'a; manque aussi le
   polymorphism, on aimerait que 'b et 'c restent polymorphes à l'appel
   de create *)
val create_arg : string ->
      ('a,tlevel,'ta) abstract_argument_type
      * ('globa,glevel,'globta) abstract_argument_type
      * ('rawa,rlevel,'rawta) abstract_argument_type

val exists_argtype : string -> bool

type argument_type =
  (* Basic types *)
  | BoolArgType
  | IntArgType
  | IntOrVarArgType
  | StringArgType
  | PreIdentArgType
  | IntroPatternArgType
  | IdentArgType
  | VarArgType
  | RefArgType
  (* Specific types *)
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

val genarg_tag : ('a,'b) generic_argument -> argument_type

val unquote : ('a,'co,'ta) abstract_argument_type -> argument_type

(* We'd like

  [in_generic: !b:type, !a:argument_type -> (f a) -> b generic_argument]

   with f a = b if a is Constr, f a = c if a is Tactic, otherwise f a = |a|

   [in_generic] is not typable; we replace the second argument by an absurd
   type (with no introduction rule)
*)
type an_arg_of_this_type

val in_generic : 
  argument_type -> an_arg_of_this_type -> ('a,'b) generic_argument

val in_gen :
  ('a,'co,'ta) abstract_argument_type -> 'a -> ('co,'ta) generic_argument
val out_gen :
  ('a,'co,'ta) abstract_argument_type -> ('co,'ta) generic_argument -> 'a 
