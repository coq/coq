(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genredexpr

let union_consts l1 l2 = Util.List.union (=) l1 l2 (* FIXME *)


let all_flags =
  {rBeta = true; rMatch = true; rFix = true; rCofix = true;
   rZeta = true; rDelta = true; rConst = []; rStrength = Norm; }

let make_red_flag l =
  let rec add_flag red = function
    | [] -> red
    | FHead :: lf -> add_flag { red with rStrength = Head } lf
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
     rZeta = false; rDelta = false; rConst = []; rStrength = Norm; }
    l

let make_red_flag = function
  | [FHead] -> { all_flags with rStrength = Head }
  | l -> make_red_flag l

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
  | ExtraRedExpr _ | Red | Hnf as x -> x
