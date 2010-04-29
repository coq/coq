(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Term
open Environ
(*i*)

(************************************************************************)
(*s Reduction functions *)

val whd_betaiotazeta        : env -> constr -> constr
val whd_betadeltaiota       : env -> constr -> constr
val whd_betadeltaiota_nolet : env -> constr -> constr

(************************************************************************)
(*s conversion functions *)

exception NotConvertible
exception NotConvertibleVect of int
type 'a conversion_function = env -> 'a -> 'a -> unit

type conv_pb = CONV | CUMUL

val conv           : constr conversion_function
val conv_leq       : constr conversion_function
val conv_leq_vecti : constr array conversion_function

val vm_conv : conv_pb -> constr conversion_function

(************************************************************************)

(* Builds an application node, reducing beta redexes it may produce. *)
val beta_appvect : constr -> constr array -> constr

(* Builds an application node, reducing the [n] first beta-zeta redexes. *)
val betazeta_appvect : int -> constr -> constr array -> constr

(* Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a] *)
val hnf_prod_applist : env -> constr -> constr list -> constr


(************************************************************************)
(*s Recognizing products and arities modulo reduction *)

val dest_prod       : env -> constr -> rel_context * constr
val dest_prod_assum : env -> constr -> rel_context * constr

val dest_arity : env -> constr -> arity
val is_arity   : env -> constr -> bool
