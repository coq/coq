(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Evd
open Environ
open Rawterm
open Pattern
(*i*)

(* Translation from AST to terms. *)

(* To embed constr in Coqast.t *)
val constrIn : constr -> Coqast.t
val constrOut : Coqast.t -> constr

val interp_rawconstr     : evar_map -> env -> Coqast.t -> rawconstr
val interp_constr        : evar_map -> env -> Coqast.t -> constr
val interp_casted_constr : evar_map -> env -> Coqast.t -> types -> constr
val interp_type          : evar_map -> env -> Coqast.t -> types
val interp_sort          : Coqast.t -> sorts

val interp_elimination_sort : Coqast.t -> sorts_family

val interp_openconstr    :
  evar_map -> env -> Coqast.t -> (existential * constr) list * constr
val interp_casted_openconstr    :
  evar_map -> env -> Coqast.t -> constr ->
    (existential * constr) list * constr

(* [interp_type_with_implicits] extends [interp_type] by allowing
   implicits arguments in the ``rel'' part of [env]; the extra
   argument associates a list of implicit positions to identifiers
   declared in the rel_context of [env] *)
val interp_type_with_implicits : 
  evar_map -> env -> 
   (identifier * Impargs.implicits_list) list -> Coqast.t -> types

val judgment_of_rawconstr : evar_map -> env -> Coqast.t -> unsafe_judgment
val type_judgment_of_rawconstr :
  evar_map -> env -> Coqast.t -> unsafe_type_judgment

(*Interprets a constr according to two lists of instantiations (variables and
  metas), possibly casting it*)
val interp_constr_gen     :
  evar_map -> env -> (identifier * constr) list ->
    (int * constr) list -> Coqast.t -> constr option -> constr

(*Interprets a constr according to two lists of instantiations (variables and
  metas), possibly casting it, and turning unresolved evar into metas*)
val interp_openconstr_gen     :
  evar_map -> env -> (identifier * constr) list ->
    (int * constr) list -> Coqast.t -> constr option
      -> (existential * constr) list * constr

(*Interprets constr patterns according to a list of instantiations
  (variables)*)
val interp_constrpattern_gen :
  evar_map -> env -> (identifier * constr) list -> Coqast.t ->
    int list * constr_pattern

val interp_constrpattern : 
  evar_map -> env -> Coqast.t -> int list * constr_pattern

(*s Globalization of AST quotations (mainly used to get statically
    bound idents in grammar or pretty-printing rules) *)
val globalize_constr : Coqast.t -> Coqast.t
val globalize_ast    : Coqast.t -> Coqast.t
val globalize_qualid : Nametab.qualid -> Coqast.t

(* This transforms args of a qualid keyword into a qualified ident *)
(* it does no relocation *)
val interp_qualid : Coqast.t list -> Nametab.qualid

(* Translation rules from V6 to V7:

constr_of_com_casted -> interp_casted_constr
constr_of_com_sort   -> interp_type
constr_of_com        -> interp_constr
rawconstr_of_com     -> interp_rawconstr  [+ env instead of sign]
type_of_com          -> types_of_com Evd.empty
constr_of_com1 true  -> interp_type
*)
