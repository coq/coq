(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

type t = Id.Pred.t * Cpred.t

let empty = (Id.Pred.empty, Cpred.empty)
let full = (Id.Pred.full, Cpred.full)
let var_full = (Id.Pred.full, Cpred.empty)
let cst_full = (Id.Pred.empty, Cpred.full)
