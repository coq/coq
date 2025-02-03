(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Evaluable references (whose transparency can be controlled) *)

open Names

type t =
  | EvalVarRef of Id.t
  | EvalConstRef of Constant.t
  | EvalProjectionRef of Projection.Repr.t

val map : (Id.t -> Id.t) -> (Constant.t -> Constant.t) ->
  (Projection.Repr.t -> Projection.Repr.t) -> t -> t

val equal : Environ.env -> t -> t -> bool

val to_kevaluable : t -> Conv_oracle.evaluable
