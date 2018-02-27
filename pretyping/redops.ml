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
