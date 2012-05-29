(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val make_red_flag :
 Tacexpr.glob_red_flag list ->
 (Libnames.reference Misctypes.or_by_notation) Glob_term.glob_red_flag

val pr_move_location :
  ('a -> Pp.std_ppcmds) -> 'a Tacexpr.move_location -> Pp.std_ppcmds
