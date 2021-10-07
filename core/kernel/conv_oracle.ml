(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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
let pr_level = function
  | Expand -> Pp.str "expand"
  | Level 0 -> Pp.str "transparent"
  | Level n -> Pp.int n
  | Opaque -> Pp.str "opaque"

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
  cst_opacity : level Cmap.t;
  var_trstate : Id.Pred.t;
  cst_trstate : Cpred.t;
}

let empty = {
  var_opacity = Id.Map.empty;
  cst_opacity = Cmap.empty;
  var_trstate = Id.Pred.full;
  cst_trstate = Cpred.full;
}

let get_strategy { var_opacity; cst_opacity; _ } f = function
  | VarKey id ->
      (try Id.Map.find id var_opacity
      with Not_found -> default)
  | ConstKey c ->
      (try Cmap.find (f c) cst_opacity
      with Not_found -> default)
  | RelKey _ -> Expand

let set_strategy ({ var_opacity; cst_opacity; _ } as oracle) k l =
  match k with
  | VarKey id ->
    let var_opacity =
      if is_default l then Id.Map.remove id var_opacity
      else Id.Map.add id l var_opacity
    in
    let var_trstate = match l with
    | Opaque -> Id.Pred.remove id oracle.var_trstate
    | _ -> Id.Pred.add id oracle.var_trstate
    in
    { oracle with var_opacity; var_trstate; }
  | ConstKey c ->
    let cst_opacity =
      if is_default l then Cmap.remove c cst_opacity
      else Cmap.add c l cst_opacity
    in
    let cst_trstate = match l with
    | Opaque -> Cpred.remove c oracle.cst_trstate
    | _ -> Cpred.add c oracle.cst_trstate
    in
    { oracle with cst_opacity; cst_trstate; }
  | RelKey _ -> CErrors.user_err Pp.(str "set_strategy: RelKey")

let fold_strategy f { var_opacity; cst_opacity; _ } accu =
  let fvar id lvl accu = f (VarKey id) lvl accu in
  let fcst cst lvl accu = f (ConstKey cst) lvl accu in
  let accu = Id.Map.fold fvar var_opacity accu in
  Cmap.fold fcst cst_opacity accu

let get_transp_state { var_trstate; cst_trstate; _ } =
  { TransparentState.tr_var = var_trstate; tr_cst = cst_trstate }

let dep_order l2r k1 k2 = match k1, k2 with
| RelKey _, RelKey _ -> l2r
| RelKey _, (VarKey _ | ConstKey _) -> true
| VarKey _, RelKey _ -> false
| VarKey _, VarKey _ -> l2r
| VarKey _, ConstKey _ -> true
| ConstKey _, (RelKey _ | VarKey _) -> false
| ConstKey _, ConstKey _ -> l2r

(* Unfold the first constant only if it is "more transparent" than the
   second one. In case of tie, use the recommended default. *)
let oracle_order f o l2r k1 k2 =
  match get_strategy o f k1, get_strategy o f k2 with
  | Expand, Expand -> dep_order l2r k1 k2
  | Expand, (Opaque | Level _) -> true
  | (Opaque | Level _), Expand -> false
  | Opaque, Opaque -> dep_order l2r k1 k2
  | Level _, Opaque -> true
  | Opaque, Level _ -> false
  | Level n1, Level n2 ->
     if Int.equal n1 n2 then dep_order l2r k1 k2
     else n1 < n2

let get_strategy o = get_strategy o (fun x -> x)
