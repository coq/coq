(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* We define some high-level properties of vernacular commands, used
   mainly by the UI components *)

open Vernacexpr

(* Return the vernacular command below control (Time, Timeout, Redirect, Fail).
   Beware that Fail can change many properties of the underlying command, since
   a success of Fail means the command was backtracked over. *)
val under_control : vernac_control -> vernac_expr

val has_Fail : vernac_control -> bool

val is_navigation_vernac : vernac_control -> bool
val is_deep_navigation_vernac : vernac_control -> bool
val is_reset : vernac_control -> bool
val is_debug : vernac_control -> bool
val is_undo : vernac_control -> bool

