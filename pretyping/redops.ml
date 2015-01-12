(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genredexpr

let union_consts l1 l2 = Util.List.union Pervasives.(=) l1 l2 (* FIXME *)

let make_red_flag l =
  let rec add_flag red = function
    | [] -> red
    | FBeta :: lf -> add_flag { red with rBeta = true } lf
    | FIota :: lf -> add_flag { red with rIota = true } lf
    | FZeta :: lf -> add_flag { red with rZeta = true } lf
    | FConst l :: lf ->
	if red.rDelta then
	  Errors.error
	    "Cannot set both constants to unfold and constants not to unfold";
        add_flag { red with rConst = union_consts red.rConst l } lf
    | FDeltaBut l :: lf ->
	if red.rConst <> [] && not red.rDelta then
	  Errors.error
	    "Cannot set both constants to unfold and constants not to unfold";
        add_flag
          { red with rConst = union_consts red.rConst l; rDelta = true }
          lf
  in
  add_flag
    {rBeta = false; rIota = false; rZeta = false; rDelta = false; rConst = []}
    l


let all_flags =
  {rBeta = true; rIota = true; rZeta = true; rDelta = true; rConst = []}
