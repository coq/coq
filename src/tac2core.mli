(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Tac2env
open Tac2expr

(** {5 Hardwired data} *)

module Core :
sig

val t_list : type_constant
val c_nil : ltac_constructor
val c_cons : ltac_constructor

val t_int : type_constant
val t_option : type_constant
val t_string : type_constant
val t_array : type_constant

val t_bindings : type_constant
val c_no_bindings : ltac_constructor
val c_implicit_bindings : ltac_constant
val c_explicit_bindings : ltac_constant

val t_qhyp : type_constant
val c_anon_hyp : ltac_constructor
val c_named_hyp : ltac_constructor

end
