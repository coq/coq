(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Names

open Ltac_plugin

open Ssrast

val ssrsettac : ist ->  Id.t -> ((ssrfwdfmt * (Ssrmatching_plugin.Ssrmatching.cpattern * ssrterm option)) * ssrdocc) -> v82tac

val ssrposetac : ist -> (Id.t * (ssrfwdfmt * ssrterm)) -> v82tac

val havetac :
           Ssrast.ist ->
           bool *
           ((((Ssrast.ssrclear * Ssrast.ssripat list) * Ssrast.ssripats) *
             Ssrast.ssripats) *
            (((Ssrast.ssrfwdkind * 'a) *
              ('b * (Glob_term.glob_constr * Constrexpr.constr_expr option))) *
             (bool * Tacinterp.Value.t option list))) ->
           bool ->
           bool -> v82tac
val ssrabstract :
           Tacinterp.interp_sign ->
           (Ssrast.ssrdocc * Ssrmatching_plugin.Ssrmatching.cpattern) list
           list * Ssrast.ssrclear -> v82tac

val basecuttac :
           string ->
           EConstr.t -> Goal.goal Evd.sigma -> Evar.t list Evd.sigma

val wlogtac :
  Ltac_plugin.Tacinterp.interp_sign ->
  ((Ssrast.ssrhyps * Ssrast.ssripats) * 'a) * 'b ->
  (Ssrast.ssrhyps *
     ((Ssrast.ssrhyp_or_id * string) *
        Ssrmatching_plugin.Ssrmatching.cpattern option)
       option)
    list *
    ('c *
       (Ssrast.ssrtermkind *
          (Glob_term.glob_constr * Constrexpr.constr_expr option))) ->
  Ltac_plugin.Tacinterp.Value.t Ssrast.ssrhint ->
  bool ->
  [< `Gen of Names.Id.t option option | `NoGen > `NoGen ] ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val sufftac :
  Ssrast.ist ->
  (((Ssrast.ssrhyps * Ssrast.ssripats) * Ssrast.ssripat list) *
     Ssrast.ssripat list) *
    (('a *
        (Ssrast.ssrtermkind *
           (Glob_term.glob_constr * Constrexpr.constr_expr option))) *
       (bool * Tacinterp.Value.t option list)) ->
  Tacmach.tactic

