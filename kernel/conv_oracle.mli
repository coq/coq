(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** Order on section paths for unfolding.
   If [oracle_order kn1 kn2] is true, then unfold kn1 first.
   Note: the oracle does not introduce incompleteness, it only
   tries to postpone unfolding of "opaque" constants. *)
val oracle_order : bool -> 'a tableKey -> 'a tableKey -> bool

(** Priority for the expansion of constant in the conversion test.
 * Higher levels means that the expansion is less prioritary.
 * (And Expand stands for -oo, and Opaque +oo.)
 * The default value (transparent constants) is [Level 0].
 *)
type level = Expand | Level of int | Opaque
val transparent : level

val get_strategy : 'a tableKey -> level

(** Sets the level of a constant.
 * Level of RelKey constant cannot be set. *)
val set_strategy : 'a tableKey -> level -> unit

val get_transp_state : unit -> transparent_state

(****************************
   Summary operations *)
type oracle
val init     : unit -> unit
val freeze   : unit -> oracle
val unfreeze : oracle -> unit
