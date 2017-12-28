(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ssrmatching_plugin
open Ssrast
open Ssrcommon

type block_names = (int * EConstr.types array) option

(* For case/elim with eq generation: args are elim_tac introeq_tac ipats
 * elim E : "=> ipats" where E give rise to introeq_tac *)
val tclEQINTROS :
           ?ind:block_names ref ->
           ?ist:ist ->
           unit Proofview.tactic ->
           unit Proofview.tactic -> ssripats -> unit Proofview.tactic
(* special case with no eq and tactic taking ist *)
val tclINTROS :
           ist ->
           (ist -> unit Proofview.tactic) ->
           ssripats -> unit Proofview.tactic

(* move=> ipats *)
val introstac : ?ist:ist -> ssripats -> unit Proofview.tactic

val elim_intro_tac :
  Ssrast.ssripats ->
  ?ist:Tacinterp.interp_sign ->
  [> `EConstr of 'a * 'b * EConstr.t ] ->
  Ssrast.ssripat option ->
  unit Proofview.tactic ->
  bool ->
  Ssrast.ssrhyp list ->
  unit Proofview.tactic

(* "move=> top; tac top; clear top" respecting the speed *)
val with_top : (EConstr.t -> unit Proofview.tactic) -> tac_ctx tac_a

val ssrmovetac :
  Ltac_plugin.Tacinterp.interp_sign ->
  Ssrast.ssrterm list *
    (Ssrast.ssripat option *
       (((Ssrast.ssrdocc * Ssrmatching.cpattern) list
        list * Ssrast.ssrclear) *
          Ssrast.ssripats)) ->
  unit Proofview.tactic

val movehnftac : unit Proofview.tactic

val with_dgens :
  (Ssrast.ssrdocc * Ssrmatching.cpattern) list
   list * Ssrast.ssrclear ->
  ((Ssrast.ssrdocc * Ssrmatching.cpattern) list ->
   Ssrast.ssrdocc * Ssrmatching.cpattern ->
   Ltac_plugin.Tacinterp.interp_sign -> unit Proofview.tactic) ->
  Ltac_plugin.Tacinterp.interp_sign -> unit Proofview.tactic

val ssrcasetac :
  Ltac_plugin.Tacinterp.interp_sign ->
  Ssrast.ssrterm list *
    (Ssrast.ssripat option *
       (((Ssrast.ssrdocc * Ssrmatching.cpattern) list list * Ssrast.ssrclear) *
          Ssrast.ssripats)) ->
  unit Proofview.tactic

val ssrapplytac :
  Tacinterp.interp_sign ->
  Ssrast.ssrterm list *
    ('a *
       ((((Ssrast.ssrhyps option * Ssrmatching_plugin.Ssrmatching.occ) *
            (Ssrast.ssrtermkind * Tacexpr.glob_constr_and_expr))
           list list * Ssrast.ssrhyps) *
          Ssrast.ssripats)) ->
  unit Proofview.tactic
