(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Util

(* modified CiME *)
open Finite_ord

(* CiME *)
open Orderings_generalities

module Prec = Finite_ord.Make (KNord)

type precedence = Prec.t

type result = Equivalent | Smaller | Greater | Uncomparable

(* precedence where equal names are Equivalent
   and distinct names are Uncomparable *)
let empty_prec = Prec.identity_ordering

let compare prec kn kn' =
  match Prec.compare prec kn kn' with
    | Orderings_generalities.Equivalent -> Equivalent
    | Orderings_generalities.Less_than -> Smaller
    | Orderings_generalities.Greater_than -> Greater
    | Orderings_generalities.Uncomparable -> Uncomparable
    | _ -> anomaly "Precedence.compare"

let is_equiv prec kn kn' =
  Prec.compare prec kn kn' = Orderings_generalities.Equivalent

let is_smaller prec kn kn' =
  Prec.compare prec kn kn' = Orderings_generalities.Less_than

let is_greater prec kn kn' =
  Prec.compare prec kn kn' = Orderings_generalities.Greater_than

let is_smaller_eq prec kn kn' =
  match Prec.compare prec kn kn' with
    | Orderings_generalities.Less_than
    | Orderings_generalities.Equivalent -> true
    | _ -> false

let is_greater_eq prec kn kn' =
  match Prec.compare prec kn kn' with
    | Orderings_generalities.Greater_than
    | Orderings_generalities.Equivalent -> true
    | _ -> false

let are_uncomparable prec kn kn' =
  Prec.compare prec kn kn' = Orderings_generalities.Uncomparable

exception Incompatible = Finite_ord.Incompatible

let add_equiv = Prec.add_equiv
let add_greater = Prec.add_greater

let add_smaller prec kn kn' = add_greater prec kn' kn

let add_prec = function
  | Equivalent -> add_equiv
  | Smaller -> add_smaller
  | Greater -> add_greater
  | _ -> invalid_arg "add_prec"

type prec_def = result * kernel_name list

let add_prec_list kn prec (op,l) =
  let f prec' kn' = add_prec op prec' kn kn' in
  List.fold_left f prec l
