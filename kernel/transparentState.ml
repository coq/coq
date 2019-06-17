(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

type t = {
  tr_var : Id.Pred.t;
  tr_cst : Cpred.t;
}

let empty = {
  tr_var = Id.Pred.empty;
  tr_cst = Cpred.empty;
}

let full = {
  tr_var = Id.Pred.full;
  tr_cst = Cpred.full;
}

let var_full = {
  tr_var = Id.Pred.full;
  tr_cst = Cpred.empty;
}

let cst_full = {
  tr_var = Id.Pred.empty;
  tr_cst = Cpred.full;
}

let is_empty ts =
  Id.Pred.is_empty ts.tr_var && Cpred.is_empty ts.tr_cst

let is_transparent_variable ts id =
  Id.Pred.mem id ts.tr_var

let is_transparent_constant ts cst =
  Cpred.mem cst ts.tr_cst
