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

type t = {
  tr_var : Id.Pred.t;
  tr_cst : Cpred.t;
  tr_prj : PRpred.t;
}

let empty = {
  tr_var = Id.Pred.empty;
  tr_cst = Cpred.empty;
  tr_prj = PRpred.empty;
}

let full = {
  tr_var = Id.Pred.full;
  tr_cst = Cpred.full;
  tr_prj = PRpred.full;
}

let is_empty ts =
  Id.Pred.is_empty ts.tr_var &&
  Cpred.is_empty ts.tr_cst &&
  PRpred.is_empty ts.tr_prj

let is_transparent_variable ts id =
  Id.Pred.mem id ts.tr_var

let is_transparent_constant ts cst =
  Cpred.mem cst ts.tr_cst

let is_transparent_projection ts p =
  PRpred.mem p ts.tr_prj

(* Debugging *)

open Util
open Pp

let pr_predicate pr_elt (b, elts) =
  let pr_elts = prlist_with_sep spc pr_elt elts in
    if b then
      str"all" ++
        (if List.is_empty elts then mt () else str" except: " ++ pr_elts)
    else
      if List.is_empty elts then str"none" else pr_elts

let pr_cpred p = pr_predicate Names.Constant.print (Cpred.elements p)
let pr_idpred p = pr_predicate Id.print (Id.Pred.elements p)

let debug_pr_transparent_state ts =
  hv 0 (str"VARIABLES: " ++ pr_idpred ts.tr_var ++ spc () ++
        str"CONSTANTS: " ++ pr_cpred ts.tr_cst)
