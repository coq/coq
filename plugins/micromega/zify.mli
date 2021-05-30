(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type S = sig
  val register : Libnames.qualid -> unit
  val print : unit -> unit
end

module InjTable : S
module UnOp : S
module BinOp : S
module CstOp : S
module BinRel : S
module PropBinOp : S
module PropUnOp : S
module BinOpSpec : S
module UnOpSpec : S
module Saturate : S

val zify_tac : unit Proofview.tactic
val saturate : unit Proofview.tactic
val iter_specs : unit Proofview.tactic
val assert_inj : EConstr.constr -> unit Proofview.tactic
val iter_let : Ltac_plugin.Tacinterp.Value.t -> unit Proofview.tactic
val elim_let : unit Proofview.tactic

val declared_term :
     Environ.env
  -> Evd.evar_map
  -> EConstr.t
  -> EConstr.t array
  -> EConstr.constr * EConstr.t array
