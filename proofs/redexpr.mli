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

(* Call by value strategy (uses virtual machine) *)
val cbv_vm : reduction_function

type red_expr = (constr, evaluable_global_reference) red_expr_gen

val reduction_of_red_expr : red_expr -> reduction_function

val declare_red_expr : string -> reduction_function -> unit

(* Opaque and Transparent commands. *)
val set_opaque_const      : constant -> unit
val set_transparent_const : constant -> unit

val set_opaque_var      : identifier -> unit
val set_transparent_var : identifier -> unit
