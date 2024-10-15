(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Sets of names *)
type t = {
  tr_var : Id.Pred.t;
  tr_cst : Cpred.t;
  tr_prj : PRpred.t;
}

val empty : t
(** Everything opaque *)

val full : t
(** Everything transparent *)

val is_empty : t -> bool

val is_transparent_variable : t -> Id.t -> bool
val is_transparent_constant : t -> Constant.t -> bool
val is_transparent_projection : t -> Projection.Repr.t -> bool
