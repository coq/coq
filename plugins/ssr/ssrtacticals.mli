(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)


val tclSEQAT :
  Ltac_plugin.Tacinterp.interp_sign ->
  Ltac_plugin.Tacinterp.Value.t ->
  Ssrast.ssrdir ->
  int Misctypes.or_var *
    (('a * Ltac_plugin.Tacinterp.Value.t option list) *
       Ltac_plugin.Tacinterp.Value.t option) ->
  Tacmach.tactic

val tclCLAUSES :
  unit Proofview.tactic ->
  (Ssrast.ssrhyps *
     ((Ssrast.ssrhyp_or_id * string) *
        Ssrmatching_plugin.Ssrmatching.cpattern option)
       option)
    list * Ssrast.ssrclseq ->
  unit Proofview.tactic

val hinttac :
           Tacinterp.interp_sign ->
           bool -> bool * Tacinterp.Value.t option list -> Ssrast.v82tac

val ssrdotac :
  Ltac_plugin.Tacinterp.interp_sign ->
  ((int Misctypes.or_var * Ssrast.ssrmmod) *
     (bool * Ltac_plugin.Tacinterp.Value.t option list)) *
    ((Ssrast.ssrhyps *
        ((Ssrast.ssrhyp_or_id * string) *
           Ssrmatching_plugin.Ssrmatching.cpattern option)
          option)
       list * Ssrast.ssrclseq) ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

