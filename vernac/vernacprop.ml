(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* We define some high-level properties of vernacular commands, used
   mainly by the UI components *)

open Vernacexpr

let has_query_control { CAst.v } =
  List.exists (function ControlFail | ControlSucceed -> true | _ -> false) v.control

(* Navigation commands are allowed in a coqtop session but not in a .v file *)
let is_navigation_vernac = function
  | VernacSynPure (VernacResetInitial | VernacResetName _ | VernacBack _) -> true
  | _ -> false

(* NB: Reset is now allowed again as asked by A. Chlipala *)
let is_reset = function
  | VernacSynPure (VernacResetInitial | VernacResetName _) -> true
  | _ -> false

let is_debug = function
  | VernacSynterp (VernacSetOption (_, ["Ltac";"Debug"], _)) -> true
  | _ -> false

let is_undo = function
  | VernacSynPure (VernacUndo _ | VernacUndoTo _) -> true
  | _ -> false
