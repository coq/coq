(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)


val tclSEQAT :
  Ltac_plugin.Tacinterp.interp_sign ->
  Ltac_plugin.Tacinterp.Value.t ->
  Ssrast.ssrdir ->
  int Misctypes.or_var *
    (('a * Ltac_plugin.Tacinterp.Value.t option list) *
       Ltac_plugin.Tacinterp.Value.t option) ->
  unit Proofview.tactic

val tclCLAUSES :
  Ltac_plugin.Tacinterp.interp_sign ->
  unit Proofview.tactic ->
  (Ssrast.ssrhyps *
     ((Ssrast.ssrhyp_or_id * string) *
        Ssrmatching_plugin.Ssrmatching.cpattern option)
       option)
    list * Ssrast.ssrclseq ->
  unit Proofview.tactic

val hinttac :
           Tacinterp.interp_sign ->
           bool -> bool * Tacinterp.Value.t option list -> unit Proofview.tactic

val ssrdotac :
  Ltac_plugin.Tacinterp.interp_sign ->
  ((int Misctypes.or_var * Ssrast.ssrmmod) *
     (bool * Ltac_plugin.Tacinterp.Value.t option list)) *
    ((Ssrast.ssrhyps *
        ((Ssrast.ssrhyp_or_id * string) *
           Ssrmatching_plugin.Ssrmatching.cpattern option)
          option)
       list * Ssrast.ssrclseq) ->
  unit Proofview.tactic

