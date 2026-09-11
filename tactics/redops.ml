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
   rZeta = true; rDelta = true; rConst = []; rStrength = Norm;
   rNoOpaques = false;
  }

let make_red_flag l =
  let add_flag red = function
    | FHead -> { red with rStrength = Head }
    | FBeta -> { red with rBeta = true }
    | FMatch -> { red with rMatch = true }
    | FFix -> { red with rFix = true }
    | FCofix -> { red with rCofix = true }
    | FZeta -> { red with rZeta = true }
    | FConst l ->
      let () = if red.rDelta then
          CErrors.user_err
            Pp.(str "Cannot set both constants to unfold and constants not to unfold")
      in
      { red with rConst = union_consts red.rConst l }
    | FDeltaBut l ->
      let () = if red.rConst <> [] && not red.rDelta then
          CErrors.user_err
            Pp.(str "Cannot set both constants to unfold and constants not to unfold")
      in
      { red with rConst = union_consts red.rConst l; rDelta = true }
    | FNoOpaques -> { red with rNoOpaques = true }
  in
  let base =
    (* if the flags are just head and/or noopaques, don't disable reduction *)
    if List.exists (function FHead | FNoOpaques -> false | _ -> true) l then
      {rBeta = false; rMatch = false; rFix = false; rCofix = false;
       rZeta = false; rDelta = false; rConst = []; rStrength = Norm;
       rNoOpaques = false;
      }
    else all_flags
  in
  List.fold_left add_flag
    base
    l

(** Mapping [red_expr_gen] *)

let map_flags f flags =
  { flags with rConst = List.map f flags.rConst }

let map_occs f (occ,e) = (occ,f e)

let map_red_expr_gen f g h i = function
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
  | UserRed usr -> UserRed (i usr)
