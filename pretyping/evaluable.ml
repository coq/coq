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

let map fvar fcst fprj = function
  | EvalVarRef v -> EvalVarRef (fvar v)
  | EvalConstRef c -> EvalConstRef (fcst c)
  | EvalProjectionRef p -> EvalProjectionRef (fprj p)

let equal env er1 er2 =
  er1 == er2 ||
  match er1, er2 with
  | EvalVarRef v1, EvalVarRef v2 ->
      Id.equal v1 v2
  | EvalConstRef c1, EvalConstRef c2 ->
      Environ.QConstant.equal env c1 c2
  | EvalProjectionRef p1, EvalProjectionRef p2 ->
      Environ.QProjection.Repr.equal env p1 p2
  | _ -> false

let to_kevaluable : t -> Conv_oracle.evaluable = fun er ->
  match er with
  | EvalVarRef v -> Conv_oracle.EvalVarRef v
  | EvalConstRef c -> Conv_oracle.EvalConstRef c
  | EvalProjectionRef p -> Conv_oracle.EvalProjectionRef p
