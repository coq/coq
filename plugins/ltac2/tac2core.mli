(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

val pf_apply : ?catch_exceptions:bool -> (Environ.env -> Evd.evar_map -> 'a Proofview.tactic) -> 'a Proofview.tactic

module type ReprType = sig
  type t
  val repr : t Tac2ffi.repr
  val prefix : string
end

module DefineMap (X : ReprType)
    (S : CSig.SetS with type elt = X.t)
    (M : CMap.ExtS with type key = X.t and module Set := S)
    () : sig end
