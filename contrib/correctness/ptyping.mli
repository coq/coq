(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term

open Ptype
open Past
open Penv

(* This module realizes type and effect inference *)

val cic_type_v : local_env -> Renamings.t -> CoqAst.t ml_type_v -> type_v

val effect_app : Renamings.t -> local_env
            -> (typing_info,'b) ProgAst.t
            -> (typing_info,constr) arg list
            -> (type_v binder list * type_c) 
             * ((identifier*identifier) list * (identifier*constr) list * bool)
             * type_c

val typed_var : Renamings.t -> local_env -> constr * constr -> variant

val type_of_expression : Renamings.t -> local_env -> constr -> constr

val states : Renamings.t -> local_env -> program -> typed_program
