(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Libnames
open Rawterm

type 'a or_var = ArgArg of 'a | ArgVar of loc * identifier

type constr_ast = Coqast.t

type open_constr = Evd.evar_map * Term.constr
type open_rawconstr = constr_ast


(* The route of a generic argument, from parsing to evaluation

              parsing        in_raw                           out_raw
    char stream ----> rawtype ----> rawconstr generic_argument ---->
                                                                   |
                                                                   | interp
                                                                   V
                          type  <---- constr generic_argument  <----
                                  out                            in

To distinguish between the uninterpreted (raw) and the interpreted
worlds, we annotate the type generic_argument by a phantom argument
which is either constr_ast or constr (actually we add also a second
argument raw_tactic_expr and tactic, but this is only for technical
reasons, because these types are undefined at the type of compilation
of Genarg).

Transformation for each type :
tag   f                          raw open type          cooked closed type

BoolArgType                    bool                     bool
IntArgType                     int                      int
IntOrVarArgType                int or_var               int
StringArgType                  string (parsed w/ "")    string
IdentArgType                   identifier               identifier         
PreIdentArgType                string (parsed w/o "")   string
QualidArgType                  qualid located           global_reference
ConstrArgType                  constr_ast               constr
ConstrMayEvalArgType               constr_ast may_eval      constr
QuantHypArgType                quantified_hypothesis    quantified_hypothesis
TacticArgType                  raw_tactic_expr          tactic
CastedOpenConstrArgType        constr_ast               open_constr
ConstrWithBindingsArgType      constr_ast with_bindings constr with_bindings
List0ArgType of argument_type
List1ArgType of argument_type
OptArgType of argument_type
ExtraArgType of string         '_a                      '_b
*)

type ('a,'co,'ta) abstract_argument_type

val rawwit_bool : (bool,'co,'ta) abstract_argument_type
val wit_bool : (bool,'co,'ta) abstract_argument_type

val rawwit_int : (int,'co,'ta) abstract_argument_type
val wit_int : (int,'co,'ta) abstract_argument_type

val rawwit_int_or_var : (int or_var,'co,'ta) abstract_argument_type
val wit_int_or_var : (int or_var,'co,'ta) abstract_argument_type

val rawwit_string : (string,'co,'ta) abstract_argument_type
val wit_string : (string,'co,'ta) abstract_argument_type

val rawwit_ident : (identifier,'co,'ta) abstract_argument_type
val wit_ident : (identifier,'co,'ta) abstract_argument_type

val rawwit_pre_ident : (string,'co,'ta) abstract_argument_type
val wit_pre_ident : (string,'co,'ta) abstract_argument_type

val rawwit_qualid : (qualid located,constr_ast,'ta) abstract_argument_type
val wit_qualid : (global_reference,constr,'ta) abstract_argument_type

val rawwit_quant_hyp : (quantified_hypothesis,'co,'ta) abstract_argument_type
val wit_quant_hyp : (quantified_hypothesis,'co,'ta) abstract_argument_type

val rawwit_constr : (constr_ast,constr_ast,'ta) abstract_argument_type
val wit_constr : (constr,constr,'ta) abstract_argument_type

val rawwit_constr_may_eval : (constr_ast may_eval,constr_ast,'ta) abstract_argument_type
val wit_constr_may_eval : (constr,constr,'ta) abstract_argument_type

val rawwit_casted_open_constr : (open_rawconstr,constr_ast,'ta) abstract_argument_type
val wit_casted_open_constr : (open_constr,constr,'ta) abstract_argument_type

val rawwit_constr_with_bindings : (constr_ast with_bindings,constr_ast,'ta) abstract_argument_type
val wit_constr_with_bindings : (constr with_bindings,constr,'ta) abstract_argument_type

val rawwit_red_expr : ((constr_ast,qualid or_metanum) red_expr_gen,constr_ast,'ta) abstract_argument_type
val wit_red_expr : ((constr,Closure.evaluable_global_reference) red_expr_gen,constr,'ta) abstract_argument_type

(* TODO: transformer tactic en extra arg *)
val rawwit_tactic : ('ta,constr_ast,'ta) abstract_argument_type
val wit_tactic : ('ta,constr,'ta) abstract_argument_type

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

(* 'a generic_argument = (Sigma t:type. t[constr/'a]) *)
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
      ('rawa,'rawco,'rawta) abstract_argument_type
      * ('a,'co,'ta) abstract_argument_type

val exists_argtype : string -> bool

type argument_type =
  | BoolArgType
  | IntArgType
  | IntOrVarArgType
  | StringArgType
  | PreIdentArgType
  | IdentArgType
  | QualidArgType
  | ConstrArgType
  | ConstrMayEvalArgType
  | QuantHypArgType
  | TacticArgType
  | CastedOpenConstrArgType
  | ConstrWithBindingsArgType
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

   in_generic is not typable; we replace the second argument by an absurd
   type (with no introduction rule)
*)
type an_arg_of_this_type

val in_generic : 
  argument_type -> an_arg_of_this_type -> ('a,'b) generic_argument

val in_gen :
  ('a,'co,'ta) abstract_argument_type -> 'a -> ('co,'ta) generic_argument
val out_gen :
  ('a,'co,'ta) abstract_argument_type -> ('co,'ta) generic_argument -> 'a 

