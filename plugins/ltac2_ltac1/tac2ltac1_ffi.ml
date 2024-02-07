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
open Tac2dyn
open Tac2ffi
open Names

let ltac1_t =
  KerName.make (MPfile (DirPath.make (List.map Id.of_string ["Ltac1";"Ltac2"])))
    (Label.of_id (Id.of_string "t"))

let val_ltac1 : Geninterp.Val.t Val.tag = Val.create "ltac1"

let ltac1_ = repr_ext val_ltac1
let of_ltac1 = repr_of ltac1_
let to_ltac1 = repr_to ltac1_
let ltac1 = typed ltac1_ Types.(!! ltac1_t)
