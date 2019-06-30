(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* We define some high-level properties of vernacular commands, used
   mainly by the UI components *)

open Vernacexpr

(* Does this vernacular involve Fail? *)
let has_Fail { CAst.v } = List.mem ControlFail v.control

(* Navigation commands are allowed in a coqtop session but not in a .v file *)
let is_navigation_vernac = function
  | VernacResetInitial
  | VernacResetName _
  | VernacBack _ -> true
  | _ -> false

(* NB: Reset is now allowed again as asked by A. Chlipala *)
let is_reset = function
  | VernacResetInitial
  | VernacResetName _ -> true
  | _ -> false

let is_debug = function
  | VernacSetOption (_, ["Ltac";"Debug"], _) -> true
  | _ -> false

let is_undo = function
  | VernacUndo _ | VernacUndoTo _ -> true
  | _ -> false
