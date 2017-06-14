(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)


val apply_top_tac : Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val inner_ssrapplytac :
  Ssrast.ssrterm list ->
  ((Ssrast.ssrhyps option * Ssrmatching_plugin.Ssrmatching.occ) *
     (Ssrast.ssrtermkind * Tacexpr.glob_constr_and_expr))
    list list ->
  Ssrast.ssrhyps ->
  Ssrast.ist ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma
