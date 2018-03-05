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

open Ssrmatching_plugin

val ssrelim :
  ?ind:(int * EConstr.types array) option ref ->
  ?is_case:bool ->
  ((Ssrast.ssrhyps option * Ssrast.ssrocc) *
     Ssrmatching.cpattern)
    list ->
  ([< `EConstr of
        Ssrast.ssrhyp list * Ssrmatching.occ *
          EConstr.constr &
          'b
   | `EGen of
       (Ssrast.ssrhyp list option *
          Ssrmatching.occ) *
         Ssrmatching.cpattern ]
   as 'a) ->
  ?elim:EConstr.constr ->
  Ssrast.ssripat option ->
  ( 'a ->
   Ssrast.ssripat option ->
   (Goal.goal Evd.sigma -> Goal.goal list Evd.sigma) ->
   bool -> Ssrast.ssrhyp list -> Tacmach.tactic) ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val elimtac : EConstr.constr -> unit Proofview.tactic

val casetac :
  EConstr.constr ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val is_injection_case : EConstr.t -> Goal.goal Evd.sigma -> bool
val perform_injection :
  EConstr.constr ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val ssrscasetac :
  EConstr.constr ->
  unit Proofview.tactic

val ssrscase_or_inj_tac :
  EConstr.constr ->
  unit Proofview.tactic
