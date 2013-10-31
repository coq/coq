(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Bruno Barras as part of the rewriting of the conversion
   algorithm, Nov 2001 *)

open Names

(* Priority for the expansion of constant in the conversion test.
 * Higher levels means that the expansion is less prioritary.
 * (And Expand stands for -oo, and Opaque +oo.)
 * The default value is [Level 100].
 *)
type level = Expand | Level of int | Opaque
let default = Level 0
let is_default = function
| Level 0 -> true
| _ -> false
let transparent = default
let is_transparent = function
| Level 0 -> true
| _ -> false

type oracle = {
  var_opacity : level Id.Map.t;
  cst_opacity : level Cmap.t
}

let empty = { var_opacity = Id.Map.empty; cst_opacity = Cmap.empty }

let get_strategy { var_opacity; cst_opacity } = function
  | VarKey id ->
      (try Id.Map.find id var_opacity
      with Not_found -> default)
  | ConstKey c ->
      (try Cmap.find c cst_opacity
      with Not_found -> default)
  | RelKey _ -> Expand

let set_strategy ({ var_opacity; cst_opacity } as oracle) k l =
  match k with
  | VarKey id ->
      { oracle with var_opacity =
          if is_default l then Id.Map.remove id var_opacity
          else Id.Map.add id l var_opacity }
  | ConstKey c ->
      { oracle with cst_opacity =
          if is_default l then Cmap.remove c cst_opacity
          else Cmap.add c l cst_opacity }
  | RelKey _ -> Errors.error "set_strategy: RelKey"

let get_transp_state { var_opacity; cst_opacity } =
  (Id.Map.fold
    (fun id l ts -> if  l=Opaque then Id.Pred.remove id ts else ts)
    var_opacity Id.Pred.full,
   Cmap.fold
    (fun c l ts -> if  l=Opaque then Cpred.remove c ts else ts)
    cst_opacity Cpred.full)

(* Unfold the first constant only if it is "more transparent" than the
   second one. In case of tie, expand the second one. *)
let oracle_order o l2r k1 k2 =
  match get_strategy o k1, get_strategy o k2 with
    | Expand, _ -> true
    | Level n1, Opaque -> true
    | Level n1, Level n2 -> n1 < n2
    | _ -> l2r (* use recommended default *)
