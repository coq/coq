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
open Evd

type 'a and_short_name = 'a * identifier located option

type 'a or_by_notation = AN of 'a | ByNotation of loc * string

(* In globalize tactics, we need to keep the initial [constr_expr] to recompute*)
(* in the environment by the effective calls to Intro, Inversion, etc *)
(* The [constr_expr] field is [None] in TacDef though *)
type rawconstr_and_expr = rawconstr * constr_expr option

type open_constr_expr = unit * constr_expr
type open_rawconstr = unit * rawconstr_and_expr

type 'a with_ebindings = 'a * open_constr bindings

type intro_pattern_expr =
  | IntroOrAndPattern of case_intro_pattern_expr
  | IntroWildcard
  | IntroIdentifier of identifier
  | IntroAnonymous
  | IntroFresh of identifier
and case_intro_pattern_expr = intro_pattern_expr list list

val pr_intro_pattern : intro_pattern_expr -> Pp.std_ppcmds
val pr_case_intro_pattern : case_intro_pattern_expr -> Pp.std_ppcmds

(* The route of a generic argument, from parsing to evaluation

\begin{verbatim}
             parsing        in_raw                              out_raw
   char stream ----> rawtype ----> constr_expr generic_argument --------|
                          encapsulation                         decaps  |
                                                                        |
                                                                        V
                                                                     rawtype
                                                                        |
                                                         globalization  |
                                                                        V
                                                                    glob_type
                                                                        |
                                                                 encaps |
                                                                in_glob |
                                                                        V
                                                     rawconstr generic_argument
                                                                        |
        out                          in                        out_glob |
  type <--- constr generic_argument <---- type <------ rawtype <--------|
    |  decaps                       encaps      interp           decaps
    |
    V
effective use
\end{verbatim}

To distinguish between the uninterpreted (raw), globalized and 
interpreted worlds, we annotate the type [generic_argument] by a
phantom argument which is either [constr_expr], [rawconstr] or
[constr].

Transformation for each type :
\begin{verbatim}
tag                            raw open type            cooked closed type

BoolArgType                    bool                      bool
IntArgType                     int                       int
IntOrVarArgType                int or_var                int
StringArgType                  string (parsed w/ "")     string
PreIdentArgType                string (parsed w/o "")    (vernac only)
IdentArgType                   identifier                identifier
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
\end{verbatim}
*)

(* All of [rlevel], [glevel] and [tlevel] must be non convertible 
   to ensure the injectivity of the type inference from type
   ['co generic_argument] to [('a,'co) abstract_argument_type];
   this guarantees that, for 'co fixed, the type of
   out_gen is monomorphic over 'a, hence type-safe 
*)

type raw = <constr:constr_expr; 
            reference:reference;
	    sort:rawsort;
	    may_eval:(constr_expr,reference or_by_notation) may_eval;
	    open_constr:open_constr_expr;
	    with_bindings:constr_expr with_bindings;
	    bindings:constr_expr bindings;
	    red_expr:(constr_expr,reference or_by_notation) red_expr_gen>
type glob = <constr:rawconstr_and_expr; 
             reference:global_reference located or_var;
	     sort:rawsort;
	     may_eval:(rawconstr_and_expr,evaluable_global_reference and_short_name or_var) may_eval;
	     open_constr:open_rawconstr;
	     with_bindings:rawconstr_and_expr with_bindings;
	     bindings:rawconstr_and_expr bindings;
	     red_expr:(rawconstr_and_expr,evaluable_global_reference and_short_name or_var) red_expr_gen>
type typed = <constr:open_constr; 
	      reference:global_reference;
	      sort:sorts;
	      may_eval:constr;
	      open_constr:open_constr;
	      with_bindings:constr with_ebindings;
	      bindings:open_constr bindings;
	      red_expr:(constr,evaluable_global_reference) red_expr_gen>

type 'l level

val rlevel : raw level
val glevel : glob level
val tlevel : typed level

type ('a,'co) abstract_argument_type

type something
val wit_any : 'l level -> (something, 'l) abstract_argument_type

val wit_bool : 'l level -> (bool,'l) abstract_argument_type

val wit_int : 'l level -> (int,'l) abstract_argument_type

val wit_int_or_var : 'l level -> (int or_var,'l) abstract_argument_type

val wit_string : 'l level -> (string,'l) abstract_argument_type

val wit_pre_ident : 'l level -> (string,'l) abstract_argument_type

val wit_intro_pattern : 'l level -> (intro_pattern_expr,'l) abstract_argument_type

val wit_ident : 'l level -> (identifier,'l) abstract_argument_type

val wit_var : 'l level -> (identifier,'l) abstract_argument_type

val wit_ref : (<reference:'r;..> as 'l) -> ('r,'l) abstract_argument_type

val wit_quant_hyp : 'l level -> (quantified_hypothesis,'l) abstract_argument_type

val wit_sort : (<sort:'r;..> as 'l) level -> ('s,'l) abstract_argument_type

val wit_constr : (<constr:'c;..> as 'l) level -> ('c,'l) abstract_argument_type

val wit_constr_may_eval : (<may_eval:'m;..> as 'l) level -> ('m,'l) abstract_argument_type

val wit_open_constr_gen : (<open_constr:'o;..> as 'l) level -> bool -> ('o,'l) abstract_argument_type

val wit_open_constr : (<open_constr:'o;..> as 'l) level -> ('o,'l) abstract_argument_type 

val wit_casted_open_constr : (<open_constr:'o;..> as 'l) level -> ('o,'l) abstract_argument_type 


val wit_constr_with_bindings : (<with_bindings:'w;..> as 'l) level -> ('o,'l) abstract_argument_type

val wit_bindings : (<bindings:'b;..> as 'l) level -> ('o,'l) abstract_argument_type

val wit_red_expr : (<red_expr:'r;..> as 'l) level -> ('o,'l) abstract_argument_type

val wit_list0 :
  ('a,'co) abstract_argument_type -> ('a list,'co) abstract_argument_type

val wit_list1 :
  ('a,'co) abstract_argument_type -> ('a list,'co) abstract_argument_type

val wit_opt :
  ('a,'co) abstract_argument_type -> ('a option,'co) abstract_argument_type

val wit_pair :
  ('a,'co) abstract_argument_type ->
  ('b,'co) abstract_argument_type ->
      ('a * 'b,'co) abstract_argument_type

(* ['a generic_argument] = (Sigma t:type. t[[constr/'a]]) *)
type 'a generic_argument


(*

val fold_list0 : 
 ('a generic_argument -> 'c -> 'c) -> 'a generic_argument -> 'c -> 'c

val fold_list1 : 
 ('a generic_argument -> 'c -> 'c) -> 'a generic_argument -> 'c -> 'c

val fold_opt :
 ('a generic_argument -> 'c) -> 'c -> 'a generic_argument -> 'c

val fold_pair :
 ('a generic_argument -> 'a generic_argument -> 'c) -> 
      'a generic_argument -> 'c

(* [app_list0] fails if applied to an argument not of tag [List0 t]
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

(* create a new generic type of argument: force to associate
   unique ML types at each of the three levels *)
val create_arg : string ->
      ('a,tlevel) abstract_argument_type
      * ('globa,glevel) abstract_argument_type
      * ('rawa,rlevel) abstract_argument_type

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

val genarg_tag : 'a generic_argument -> argument_type

val unquote : ('a,'co) abstract_argument_type -> argument_type

val in_gen :
  ('a,'co) abstract_argument_type -> 'a -> 'co generic_argument
val out_gen :
  ('a,'co) abstract_argument_type -> 'co generic_argument -> 'a 


(* [in_generic] is used in combination with camlp4 [Gramext.action] magic

   [in_generic: !l:type, !a:argument_type -> |a|_l -> 'l generic_argument]

   where |a|_l is the interpretation of a at level l

   [in_generic] is not typable; we replace the second argument by an absurd
   type (with no introduction rule)
*)
type an_arg_of_this_type

val in_generic : 
  argument_type -> an_arg_of_this_type -> 'co generic_argument

*)
