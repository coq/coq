(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ltac2_plugin
open Tac2ffi
open Tac2val

val to_ltac1 : valexpr -> Geninterp.Val.t
val of_ltac1 : Geninterp.Val.t -> valexpr
val ltac1 : Geninterp.Val.t repr annotated
