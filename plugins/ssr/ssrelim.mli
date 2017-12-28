(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Ssrmatching_plugin

val ssrelim :
  ?ind:(int * EConstr.types array) option ref ->
  ?is_case:bool ->
  ?ist:Ltac_plugin.Tacinterp.interp_sign ->
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
  (?ist:Ltac_plugin.Tacinterp.interp_sign ->
   'a ->
   Ssrast.ssripat option ->
   unit Proofview.tactic ->
   bool -> Ssrast.ssrhyp list -> unit Proofview.tactic) ->
  unit Proofview.tactic

val elimtac :
  EConstr.constr ->
  unit Proofview.tactic
val casetac :
  EConstr.constr ->
  unit Proofview.tactic

val is_injection_case : EConstr.t -> Goal.goal Evd.sigma -> bool
val perform_injection :
  EConstr.constr ->
  unit Proofview.tactic

val ssrscasetac :
  bool ->
  EConstr.constr ->
  unit Proofview.tactic
