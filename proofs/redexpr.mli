(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Term
open Closure
open Rawterm
open Reductionops


type red_expr = (constr, evaluable_global_reference) red_expr_gen

val out_with_occurrences : 'a with_occurrences -> int list * 'a

val reduction_of_red_expr : red_expr -> reduction_function * cast_kind
(* [true] if we should use the vm to verify the reduction *)

val declare_red_expr : string -> reduction_function -> unit

(* Opaque and Transparent commands. *)

val set_strategy : 'a tableKey ->  Conv_oracle.level -> unit

(* call by value normalisation function using the virtual machine *)
val cbv_vm : reduction_function
