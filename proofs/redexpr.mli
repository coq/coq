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
open Pattern
open Rawterm
open Reductionops
open Termops

type red_expr =
    (constr, evaluable_global_reference, constr_pattern) red_expr_gen

val out_with_occurrences : 'a with_occurrences -> occurrences * 'a

val reduction_of_red_expr : red_expr -> reduction_function * cast_kind
(* [true] if we should use the vm to verify the reduction *)

(* Adding a custom reduction (function to be use at the ML level)
   NB: the effect is permanent. *)
val declare_reduction : string -> reduction_function -> unit

(* Adding a custom reduction (function to be called a vernac command).
   The boolean flag is the locality. *)
val declare_red_expr : bool -> string -> red_expr -> unit

(* Opaque and Transparent commands. *)

(* Sets the expansion strategy of a constant. When the boolean is
   true, the effect is non-synchronous (i.e. it does not survive
   section and module closure). *)
val set_strategy :
  bool -> (Conv_oracle.level * evaluable_global_reference list) list -> unit

(* call by value normalisation function using the virtual machine *)
val cbv_vm : reduction_function
