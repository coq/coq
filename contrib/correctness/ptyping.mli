(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term
open Topconstr

open Ptype
open Past
open Penv

(* This module realizes type and effect inference *)

val cic_type_v : local_env -> Prename.t -> constr_expr ml_type_v -> type_v

val effect_app : Prename.t -> local_env
            -> (typing_info,'b) Past.t
            -> (typing_info,constr) arg list
            -> (type_v binder list * type_c) 
             * ((identifier*identifier) list * (identifier*constr) list * bool)
             * type_c

val typed_var : Prename.t -> local_env -> constr * constr -> variant

val type_of_expression : Prename.t -> local_env -> constr -> constr

val states : Prename.t -> local_env -> program -> typed_program
