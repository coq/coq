(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Names

open Ltac_plugin

open Ssrast

val ssrsettac :  Id.t -> ((ssrfwdfmt * (Ssrmatching_plugin.Ssrmatching.cpattern * ast_closure_term option)) * ssrdocc) -> unit Proofview.tactic

val ssrposetac : Id.t * (ssrfwdfmt * ast_closure_term) -> unit Proofview.tactic

val havetac : ist ->
           bool *
           ((((Ssrast.ssrclear option * Ssrast.ssripat list) * Ssrast.ssripats) *
             Ssrast.ssripats) *
            (((Ssrast.ssrfwdkind * 'a) * ast_closure_term) *
             (bool * Tacinterp.Value.t option list))) ->
           bool ->
           bool -> unit Proofview.tactic

type cut_kind = Have | HaveTransp | Suff
val basecuttac : cut_kind -> EConstr.t -> unit Proofview.tactic

val basesufftac : EConstr.t -> unit Proofview.tactic

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
  unit Proofview.tactic

val sufftac :
  Ssrast.ist ->
  (((Ssrast.ssrclear option * Ssrast.ssripats) * Ssrast.ssripat list) *
     Ssrast.ssripat list) *
    (('a *
        ast_closure_term) *
       (bool * Tacinterp.Value.t option list)) ->
  unit Proofview.tactic

(* pad_intro (by default false) indicates whether the intro-pattern
   "=> i..." must be turned into "=> [i...|i...|i...|]" (n+1 branches,
   assuming there are n provided tactics in the ssrhint argument
   "do [...|...|...]"; it is useful when the intro-pattern is "=> *").
   Otherwise, "=> i..." is turned into "=> [i...|]". *)
val undertac :
  ?pad_intro:bool ->
  Ltac_plugin.Tacinterp.interp_sign ->
  Ssrast.ssripats option -> Ssrequality.ssrrwarg ->
  Ltac_plugin.Tacinterp.Value.t Ssrast.ssrhint -> unit Proofview.tactic

val overtac :
  unit Proofview.tactic
