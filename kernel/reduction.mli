(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Environ
(*i*)

(***********************************************************************)
(*s Reduction functions *)

val whd_betadeltaiota       : env -> constr -> constr
val whd_betadeltaiota_nolet : env -> constr -> constr

val nf_betaiota      : constr -> constr
val hnf_stack        : env -> constr -> constr * constr list
val hnf_prod_applist : env -> types -> constr list -> types

(* Builds an application node, reducing beta redexes it may produce. *) 
val beta_appvect : constr -> constr array -> constr

(***********************************************************************)
(*s conversion functions *)

exception NotConvertible
exception NotConvertibleVect of int
type 'a conversion_function = env -> 'a -> 'a -> Univ.constraints

val conv           : types conversion_function
val conv_leq       : types conversion_function
val conv_leq_vecti : types array conversion_function

(***********************************************************************)
(*s Recognizing products and arities modulo reduction *)

val dest_prod       : env -> types -> Sign.rel_context * types
val dest_prod_assum : env -> types -> Sign.rel_context * types

val dest_arity : env -> types -> Sign.arity
val is_arity   : env -> types -> bool
