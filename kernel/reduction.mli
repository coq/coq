(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Term
open Environ
open Closure

(***********************************************************************
  s Reduction functions *)

val whd_betaiotazeta        : constr -> constr
val whd_betadeltaiota       : env -> constr -> constr
val whd_betadeltaiota_nolet : env -> constr -> constr

val nf_betaiota      : constr -> constr

(***********************************************************************
  s conversion functions *)

exception NotConvertible
exception NotConvertibleVect of int
type 'a conversion_function = env -> 'a -> 'a -> Univ.constraints
type 'a trans_conversion_function = Names.transparent_state -> env -> 'a -> 'a -> Univ.constraints

type conv_pb = CONV | CUMUL

val sort_cmp :
    conv_pb -> sorts -> sorts -> Univ.constraints -> Univ.constraints

val conv_sort      : sorts conversion_function
val conv_sort_leq  : sorts conversion_function

val trans_conv_cmp       : conv_pb -> constr trans_conversion_function
val trans_conv           :
  ?evars:(existential->constr option) -> constr trans_conversion_function
val trans_conv_leq       :
  ?evars:(existential->constr option) -> types trans_conversion_function

val conv_cmp       : conv_pb -> constr conversion_function
val conv           :
  ?evars:(existential->constr option) -> constr conversion_function
val conv_leq       :
  ?evars:(existential->constr option) -> types conversion_function
val conv_leq_vecti :
  ?evars:(existential->constr option) -> types array conversion_function

(** option for conversion *)
val set_vm_conv : (conv_pb -> types conversion_function) -> unit
val vm_conv : conv_pb -> types conversion_function

val set_default_conv : (conv_pb -> types conversion_function) -> unit
val default_conv     : conv_pb -> types conversion_function
val default_conv_leq : types conversion_function

(************************************************************************)

(** Builds an application node, reducing beta redexes it may produce. *)
val beta_appvect : constr -> constr array -> constr

(** Builds an application node, reducing the [n] first beta-zeta redexes. *)
val betazeta_appvect : int -> constr -> constr array -> constr

(** Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a] *)
val hnf_prod_applist : env -> types -> constr list -> types


(***********************************************************************
  s Recognizing products and arities modulo reduction *)

val dest_prod       : env -> types -> rel_context * types
val dest_prod_assum : env -> types -> rel_context * types

val dest_arity : env -> types -> arity
val is_arity   : env -> types -> bool
