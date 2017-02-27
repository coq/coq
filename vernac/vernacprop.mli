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

val is_navigation_vernac : vernac_expr -> bool
val is_deep_navigation_vernac : vernac_expr -> bool
val is_reset : vernac_expr -> bool
val is_query : vernac_expr -> bool
val is_debug : vernac_expr -> bool
val is_undo : vernac_expr -> bool
