(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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

val c_true : ltac_constructor
val c_false : ltac_constructor

end

val pf_apply : (Environ.env -> Evd.evar_map -> 'a Proofview.tactic) -> 'a Proofview.tactic
