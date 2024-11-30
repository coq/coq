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
open Tac2ffi
open Tac2typing_env

(* avoid mutual dependency between Tac2typing_env and Tac2expr *)
type valtype = TVar.t glb_typexpr option  (* todo: keep option? *)

type typed_valexpr = Tac2env.typed_valexpr = {
  e : valexpr;
  t : Obj.t option  (* really valtype *)
}

let wrap (t: t * TVar.t glb_typexpr) = Obj.repr t

let unwrap : Obj.t -> t * TVar.t glb_typexpr = fun o -> Obj.obj o
