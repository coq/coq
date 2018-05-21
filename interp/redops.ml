(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genredexpr

let union_consts l1 l2 = Util.List.union Pervasives.(=) l1 l2 (* FIXME *)

let make_red_flag l =
  let rec add_flag red = function
    | [] -> red
    | FBeta :: lf -> add_flag { red with rBeta = true } lf
    | FMatch :: lf -> add_flag { red with rMatch = true } lf
    | FFix :: lf -> add_flag { red with rFix = true } lf
    | FCofix :: lf -> add_flag { red with rCofix = true } lf
    | FZeta :: lf -> add_flag { red with rZeta = true } lf
    | FConst l :: lf ->
	if red.rDelta then
	  CErrors.user_err Pp.(str
	    "Cannot set both constants to unfold and constants not to unfold");
        add_flag { red with rConst = union_consts red.rConst l } lf
    | FDeltaBut l :: lf ->
	if red.rConst <> [] && not red.rDelta then
	  CErrors.user_err Pp.(str
	    "Cannot set both constants to unfold and constants not to unfold");
        add_flag
          { red with rConst = union_consts red.rConst l; rDelta = true }
          lf
  in
  add_flag
    {rBeta = false; rMatch = false; rFix = false; rCofix = false;
     rZeta = false; rDelta = false; rConst = []}
    l


let all_flags =
  {rBeta = true; rMatch = true; rFix = true; rCofix = true;
   rZeta = true; rDelta = true; rConst = []}

(** Mapping [red_expr_gen] *)

let map_flags f flags =
  { flags with rConst = List.map f flags.rConst }

let map_occs f (occ,e) = (occ,f e)

let map_red_expr_gen f g h = function
  | Fold l -> Fold (List.map f l)
  | Pattern occs_l -> Pattern (List.map (map_occs f) occs_l)
  | Simpl (flags,occs_o) ->
     Simpl (map_flags g flags, Option.map (map_occs (Util.map_union g h)) occs_o)
  | Unfold occs_l -> Unfold (List.map (map_occs g) occs_l)
  | Cbv flags -> Cbv (map_flags g flags)
  | Lazy flags -> Lazy (map_flags g flags)
  | CbvVm occs_o -> CbvVm (Option.map (map_occs (Util.map_union g h)) occs_o)
  | CbvNative occs_o -> CbvNative (Option.map (map_occs (Util.map_union g h)) occs_o)
  | Cbn flags -> Cbn (map_flags g flags)
  | ExtraRedExpr _ | Red _ | Hnf as x -> x
