(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.5 *)

(* In 8.5, "intros [|]", taken e.g. on a goal "A\/B->C", does not
   behave as "intros [H|H]" but leave instead hypotheses quantified in
   the goal, here producing subgoals A->C and B->C. *)

Unset Bracketing Last Introduction Pattern.

