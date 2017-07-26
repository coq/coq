(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Legacy proof engine. Do not use in newly written code. *)

open Evd
open Names
open Term

(** This module defines the structure of proof tree and the tactic type. So, it
   is used by [Proof_tree] and [Refiner] *)

type prim_rule =
  | Cut of bool * bool * Id.t * types
  | Refine of constr

(** Nowadays, the only rules we'll consider are the primitive rules *)

type rule = prim_rule

type goal = Goal.goal

type tactic = goal sigma -> goal list sigma
