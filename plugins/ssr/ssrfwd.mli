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

open Names

open Ltac_plugin

open Ssrast

val ssrsettac :  Id.t -> ((ssrfwdfmt * (Ssrmatching_plugin.Ssrmatching.cpattern * ast_closure_term option)) * ssrdocc) -> v82tac

val ssrposetac : Id.t * (ssrfwdfmt * ast_closure_term) -> v82tac

val havetac : ist ->
           bool *
           ((((Ssrast.ssrclear option * Ssrast.ssripat list) * Ssrast.ssripats) *
             Ssrast.ssripats) *
            (((Ssrast.ssrfwdkind * 'a) * ast_closure_term) *
             (bool * Tacinterp.Value.t option list))) ->
           bool ->
           bool -> v82tac

val basecuttac :
           string ->
           EConstr.t -> Goal.goal Evd.sigma -> Evar.t list Evd.sigma

val wlogtac :
  Ltac_plugin.Tacinterp.interp_sign ->
  ((Ssrast.ssrclear option * Ssrast.ssripats) * 'a) * 'b ->
  (Ssrast.ssrhyps *
     ((Ssrast.ssrhyp_or_id * string) *
        Ssrmatching_plugin.Ssrmatching.cpattern option)
       option)
    list *
    ('c *
       ast_closure_term) ->
  Ltac_plugin.Tacinterp.Value.t Ssrast.ssrhint ->
  bool ->
  [< `Gen of Names.Id.t option option | `NoGen > `NoGen ] ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val sufftac :
  Ssrast.ist ->
  (((Ssrast.ssrclear option * Ssrast.ssripats) * Ssrast.ssripat list) *
     Ssrast.ssripat list) *
    (('a *
        ast_closure_term) *
       (bool * Tacinterp.Value.t option list)) ->
  Tacmach.tactic

val undertac :
  Ltac_plugin.Tacinterp.interp_sign ->
  Names.Id.t list -> Ssrequality.ssrrwarg ->
  Ltac_plugin.Tacinterp.Value.t Ssrast.ssrhint -> unit Proofview.tactic

val overtac :
  unit Proofview.tactic
