(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Legacy proof engine. Do not use in newly written code. *)

open Evd
open Constr

(** This module defines the structure of proof tree and the tactic type. So, it
   is used by [Proof_tree] and [Refiner] *)

type prim_rule =
  | Refine of constr

(** Nowadays, the only rules we'll consider are the primitive rules *)

type rule = prim_rule

type goal = Goal.goal

type tactic = goal sigma -> goal list sigma
