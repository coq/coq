(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Environ
(*i*)

(************************************************************************)
(*s Reduction functions *)

val whd_betaiotazeta        : env -> constr -> constr
val whd_betadeltaiota       : env -> constr -> constr
val whd_betadeltaiota_nolet : env -> constr -> constr

val nf_betaiota      : constr -> constr

(************************************************************************)
(*s conversion functions *)

exception NotConvertible
exception NotConvertibleVect of int
type 'a conversion_function = env -> 'a -> 'a -> Univ.constraints

val conv_sort      : sorts conversion_function
val conv_sort_leq  : sorts conversion_function

val conv           : types conversion_function
val conv_leq       : types conversion_function
val conv_leq_vecti : types array conversion_function

(************************************************************************)

(* Builds an application node, reducing beta redexes it may produce. *) 
val beta_appvect : constr -> constr array -> constr

(* Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a] *)
val hnf_prod_applist : env -> types -> constr list -> types


(************************************************************************)
(*s Recognizing products and arities modulo reduction *)

val dest_prod       : env -> types -> Sign.rel_context * types
val dest_prod_assum : env -> types -> Sign.rel_context * types

val dest_arity : env -> types -> Sign.arity
val is_arity   : env -> types -> bool
