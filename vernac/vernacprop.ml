(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* We define some high-level properties of vernacular commands, used
   mainly by the UI components *)

open Vernacexpr

(* Navigation commands are allowed in a coqtop session but not in a .v file *)
let rec is_navigation_vernac = function
  | VernacResetInitial
  | VernacResetName _
  | VernacBacktrack _
  | VernacBackTo _
  | VernacBack _
  | VernacStm _ -> true
  | VernacRedirect (_, (_,c))
  | VernacTime (_,c) ->
      is_navigation_vernac c (* Time Back* is harmless *)
  | c -> is_deep_navigation_vernac c

and is_deep_navigation_vernac = function
  | VernacTimeout (_,c) | VernacFail c -> is_navigation_vernac c
  | _ -> false

(* NB: Reset is now allowed again as asked by A. Chlipala *)
let is_reset = function
  | VernacResetInitial | VernacResetName _ -> true
  | _ -> false

let is_debug cmd = match cmd with
  | VernacSetOption (["Ltac";"Debug"], _) -> true
  | _ -> false

let is_query cmd = match cmd with
  | VernacChdir None
  | VernacMemOption _
  | VernacPrintOption _
  | VernacCheckMayEval _
  | VernacGlobalCheck _
  | VernacPrint _
  | VernacSearch _
  | VernacLocate _ -> true
  | _ -> false

let is_undo cmd = match cmd with
  | VernacUndo _ | VernacUndoTo _ -> true
  | _ -> false
