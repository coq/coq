(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Cic
open Term
open Environ
(*i*)

(************************************************************************)
(*s Reduction functions *)

val whd_betaiotazeta        : constr -> constr
val whd_all       : env -> constr -> constr
val whd_allnolet : env -> constr -> constr

(************************************************************************)
(*s conversion functions *)

exception NotConvertible
exception NotConvertibleVect of int
type 'a conversion_function = env -> 'a -> 'a -> unit

type conv_pb = CONV | CUMUL

val conv           : constr conversion_function
val conv_leq       : constr conversion_function

val vm_conv : conv_pb -> constr conversion_function

(************************************************************************)

(* Builds an application node, reducing beta redexes it may produce. *)
val beta_appvect : constr -> constr array -> constr

(* Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a] *)
val hnf_prod_applist : env -> constr -> constr list -> constr


(************************************************************************)
(*s Recognizing products and arities modulo reduction *)

val dest_prod       : env -> constr -> rel_context * constr
val dest_prod_assum : env -> constr -> rel_context * constr
val dest_lam_assum  : env -> constr -> rel_context * constr


val dest_arity : env -> constr -> arity
