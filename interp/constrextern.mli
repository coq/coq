(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ *)

(*i*)
open Names
open Term
open Termops
open Sign
open Environ
open Libnames
open Nametab
open Rawterm
open Pattern
open Topconstr
(*i*)

(* Translation of pattern, cases pattern, rawterm and term into syntax
   trees for printing *)

val extern_cases_pattern : cases_pattern -> cases_pattern_expr
val extern_rawconstr : rawconstr -> constr_expr
val extern_pattern : env -> names_context -> constr_pattern -> constr_expr

(* If [b=true] in [extern_constr b env c] then the variables in the first 
   level of quantification clashing with the variables in [env] are renamed *)

val extern_constr : bool -> env -> constr -> constr_expr
val extern_ref    : global_reference -> reference

(* For debugging *)
val print_implicits : bool ref
val print_casts : bool ref
val print_arguments : bool ref
val print_evar_arguments : bool ref
val print_coercions : bool ref
val print_universes : bool ref

val with_casts : ('a -> 'b) -> 'a -> 'b
val with_implicits : ('a -> 'b) -> 'a -> 'b
val with_arguments : ('a -> 'b) -> 'a -> 'b
val with_coercions : ('a -> 'b) -> 'a -> 'b
val with_universes : ('a -> 'b) -> 'a -> 'b
