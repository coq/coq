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

open Ltac_plugin
open Ssrmatching_plugin

val tclSEQAT :
  Tacinterp.interp_sign ->
  Tacinterp.Value.t ->
  Ssrast.ssrdir ->
  int Locus.or_var *
    (('a * Tacinterp.Value.t option list) *
       Tacinterp.Value.t option) ->
  Tacmach.tactic

val tclCLAUSES :
  unit Proofview.tactic ->
  (Ssrast.ssrhyps *
     ((Ssrast.ssrhyp_or_id * string) *
        Ssrmatching.cpattern option)
       option)
    list * Ssrast.ssrclseq ->
  unit Proofview.tactic

val hinttac :
           Tacinterp.interp_sign ->
           bool -> bool * Tacinterp.Value.t option list -> Ssrast.v82tac

val ssrdotac :
  Tacinterp.interp_sign ->
  ((int Locus.or_var * Ssrast.ssrmmod) *
     (bool * Tacinterp.Value.t option list)) *
    ((Ssrast.ssrhyps *
        ((Ssrast.ssrhyp_or_id * string) *
           Ssrmatching.cpattern option)
          option)
       list * Ssrast.ssrclseq) ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

