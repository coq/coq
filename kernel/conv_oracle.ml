(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
  prj_opacity : level PRmap.t;
  var_trstate : Id.Pred.t;
  cst_trstate : Cpred.t;
  prj_trstate : PRpred.t;
}

let empty = {
  var_opacity = Id.Map.empty;
  cst_opacity = Cmap.empty;
  prj_opacity = PRmap.empty;
  var_trstate = Id.Pred.full;
  cst_trstate = Cpred.full;
  prj_trstate = PRpred.full;
}

type evaluable =
  | EvalVarRef of Id.t
  | EvalConstRef of Constant.t
  | EvalProjectionRef of Projection.Repr.t

let get_strategy { var_opacity; cst_opacity; prj_opacity; _ } = function
  | EvalVarRef id ->
      (try Id.Map.find id var_opacity
      with Not_found -> default)
  | EvalConstRef c ->
      (try Cmap.find c cst_opacity
      with Not_found -> default)
  | EvalProjectionRef p ->
      (try PRmap.find p prj_opacity
      with Not_found -> default)

let set_strategy ({var_opacity; cst_opacity; prj_opacity; _} as oracle) k l =
  match k with
  | EvalVarRef id ->
    let var_opacity =
      if is_default l then Id.Map.remove id var_opacity
      else Id.Map.add id l var_opacity
    in
    let var_trstate = match l with
    | Opaque -> Id.Pred.remove id oracle.var_trstate
    | _ -> Id.Pred.add id oracle.var_trstate
    in
    { oracle with var_opacity; var_trstate; }
  | EvalConstRef c ->
    let cst_opacity =
      if is_default l then Cmap.remove c cst_opacity
      else Cmap.add c l cst_opacity
    in
    let cst_trstate = match l with
    | Opaque -> Cpred.remove c oracle.cst_trstate
    | _ -> Cpred.add c oracle.cst_trstate
    in
    { oracle with cst_opacity; cst_trstate; }
  | EvalProjectionRef p ->
    let prj_opacity =
      if is_default l then PRmap.remove p prj_opacity
      else PRmap.add p l prj_opacity
    in
    let prj_trstate = match l with
    | Opaque -> PRpred.remove p oracle.prj_trstate
    | _ -> PRpred.add p oracle.prj_trstate
    in
    {oracle with prj_opacity; prj_trstate}

let fold_strategy f {var_opacity; cst_opacity; prj_opacity; _} accu =
  let fvar id lvl accu = f (EvalVarRef id) lvl accu in
  let fcst cst lvl accu = f (EvalConstRef cst) lvl accu in
  let fprj p lvl accu = f (EvalProjectionRef p) lvl accu in
  let accu = Id.Map.fold fvar var_opacity accu in
  let accu = Cmap.fold fcst cst_opacity accu in
  PRmap.fold fprj prj_opacity accu

let get_transp_state { var_trstate; cst_trstate; prj_trstate; _ } =
  let open TransparentState in
  { tr_var = var_trstate; tr_cst = cst_trstate ; tr_prj = prj_trstate }

let dep_order l2r k1 k2 =
  match k1, k2 with
  | None, None -> l2r
  | None, _    -> true
  | Some _, None -> false
  | Some k1, Some k2 ->
  match k1, k2 with
  | EvalVarRef _, EvalVarRef _ -> l2r
  | EvalVarRef _, (EvalConstRef _ | EvalProjectionRef _) -> true
  | EvalConstRef _, EvalVarRef _ -> false
  | EvalConstRef _, EvalProjectionRef _ -> l2r
  | EvalConstRef _, EvalConstRef _ -> l2r
  | EvalProjectionRef _, EvalVarRef _ -> false
  | EvalProjectionRef _, EvalConstRef _ -> l2r
  | EvalProjectionRef _, EvalProjectionRef _ -> l2r

(* Unfold the first constant only if it is "more transparent" than the
   second one. In case of tie, use the recommended default. *)
let oracle_order o l2r k1 k2 =
  let s1 = match k1 with None -> Expand | Some k1 -> get_strategy o k1 in
  let s2 = match k2 with None -> Expand | Some k2 -> get_strategy o k2 in
  match s1, s2 with
  | Expand, Expand -> dep_order l2r k1 k2
  | Expand, (Opaque | Level _) -> true
  | (Opaque | Level _), Expand -> false
  | Opaque, Opaque -> dep_order l2r k1 k2
  | Level _, Opaque -> true
  | Opaque, Level _ -> false
  | Level n1, Level n2 ->
     if Int.equal n1 n2 then dep_order l2r k1 k2
     else n1 < n2
