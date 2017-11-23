(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* We define some high-level properties of vernacular commands, used
   mainly by the UI components *)

open Vernacexpr

let rec under_control = function
  | VernacExpr c -> c
  | VernacRedirect (_,(_,c))
  | VernacTime (_,c)
  | VernacFail c
  | VernacTimeout (_,c) -> under_control c

let rec has_Fail = function
  | VernacExpr c -> false
  | VernacRedirect (_,(_,c))
  | VernacTime (_,c)
  | VernacTimeout (_,c) -> has_Fail c
  | VernacFail _ -> true

(* Navigation commands are allowed in a coqtop session but not in a .v file *)
let is_navigation_vernac_expr = function
  | VernacResetInitial
  | VernacResetName _
  | VernacBacktrack _
  | VernacBackTo _
  | VernacBack _ -> true
  | _ -> false

let is_navigation_vernac c =
  is_navigation_vernac_expr (under_control c)

let rec is_deep_navigation_vernac = function
  | VernacTime (_,c) -> is_deep_navigation_vernac c
  | VernacRedirect (_, (_,c))
  | VernacTimeout (_,c) | VernacFail c -> is_navigation_vernac c
  | VernacExpr _ -> false

(* NB: Reset is now allowed again as asked by A. Chlipala *)
let is_reset = function
  | VernacExpr VernacResetInitial
  | VernacExpr (VernacResetName _) -> true
  | _ -> false

let is_debug cmd = match under_control cmd with
  | VernacSetOption (["Ltac";"Debug"], _) -> true
  | _ -> false

let is_query cmd = match under_control cmd with
  | VernacChdir None
  | VernacMemOption _
  | VernacPrintOption _
  | VernacCheckMayEval _
  | VernacGlobalCheck _
  | VernacPrint _
  | VernacSearch _
  | VernacLocate _ -> true
  | _ -> false

let is_undo cmd = match under_control cmd with
  | VernacUndo _ | VernacUndoTo _ -> true
  | _ -> false
