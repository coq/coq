(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tac2env
open Tac2expr

(** {5 Hardwired data} *)

module Core :
sig

val t_list : type_constant
val c_nil : ltac_constant
val c_cons : ltac_constant

end

(** {5 Ltac2 FFI} *)

module Value :
sig

val of_unit : unit -> valexpr
val to_unit : valexpr -> unit

val of_list : valexpr list -> valexpr
val to_list : valexpr -> valexpr list

end
