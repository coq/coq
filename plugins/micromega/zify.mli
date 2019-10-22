(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Constrexpr

module type S = sig val register : constr_expr -> unit val print : unit -> unit end

module InjTable : S
module UnOp     : S
module BinOp    : S
module CstOp    : S
module BinRel   : S
module PropOp   : S
module PropUnOp : S
module Spec     : S
module Saturate : S

val zify_tac : unit Proofview.tactic
val saturate : unit Proofview.tactic
val iter_specs : Ltac_plugin.Tacinterp.Value.t -> unit Proofview.tactic
