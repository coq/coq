(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Topconstr
open Libnames
open Nametab
open Glob_term
open Errors
open Util
open Genarg
open Pattern
open Decl_kinds
open Misctypes
open Locus
open Tacexpr

let make_red_flag =
  let rec add_flag red = function
    | [] -> red
    | FBeta :: lf -> add_flag { red with rBeta = true } lf
    | FIota :: lf -> add_flag { red with rIota = true } lf
    | FZeta :: lf -> add_flag { red with rZeta = true } lf
    | FConst l :: lf ->
	if red.rDelta then
	  error
	    "Cannot set both constants to unfold and constants not to unfold";
        add_flag { red with rConst = list_union red.rConst l } lf
    | FDeltaBut l :: lf ->
	if red.rConst <> [] & not red.rDelta then
	  error
	    "Cannot set both constants to unfold and constants not to unfold";
        add_flag
	  { red with rConst = list_union red.rConst l; rDelta = true }
	  lf
  in
  add_flag
    {rBeta = false; rIota = false; rZeta = false; rDelta = false; rConst = []}

open Pp

let pr_move_location pr_id = function
  | MoveAfter id -> brk(1,1) ++ str "after " ++ pr_id id
  | MoveBefore id -> brk(1,1) ++ str "before " ++ pr_id id
  | MoveFirst -> str " at top"
  | MoveLast -> str " at bottom"
