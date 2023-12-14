(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

type oracle

val empty : oracle

(** Order on section paths for unfolding.
   If [oracle_order kn1 kn2] is true, then unfold kn1 first.
   Note: the oracle does not introduce incompleteness, it only
   tries to postpone unfolding of "opaque" constants. *)
val oracle_order :
  oracle -> bool -> Evaluable.t option -> Evaluable.t option -> bool

(** Priority for the expansion of constant in the conversion test.
 * Higher levels means that the expansion is less prioritary.
 * (And Expand stands for -oo, and Opaque +oo.)
 * The default value (transparent constants) is [Level 0].
 *)
type level = Expand | Level of int | Opaque
val pr_level : level -> Pp.t
val transparent : level

(** Check whether a level is transparent *)
val is_transparent : level -> bool

val get_strategy : oracle -> Evaluable.t -> level

(** Sets the level of a constant.
 * Level of RelKey constant cannot be set. *)
val set_strategy : oracle -> Evaluable.t -> level -> oracle

(** Fold over the non-transparent levels of the oracle. Order unspecified. *)
val fold_strategy : (Evaluable.t -> level -> 'a -> 'a) -> oracle -> 'a -> 'a

val get_transp_state : oracle -> TransparentState.t
