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
   (Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma) ->
   bool -> Ssrast.ssrhyp list -> Proof_type.tactic) ->
  Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma

val elimtac :
  EConstr.constr ->
  Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma
val casetac :
  EConstr.constr ->
  Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma

val is_injection_case : EConstr.t -> Proof_type.goal Evd.sigma -> bool
val perform_injection :
  EConstr.constr ->
  Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma

val ssrscasetac :
  bool ->
  EConstr.constr ->
  Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma
