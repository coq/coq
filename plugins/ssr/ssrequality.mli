(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open API
open Ssrmatching_plugin
open Ssrast

type ssrwkind = RWred of ssrsimpl | RWdef | RWeq
type ssrrule = ssrwkind * ssrterm
type ssrrwarg = (ssrdir * ssrmult) * ((ssrdocc * Ssrmatching.rpattern option) * ssrrule)

val dir_org : ssrdir -> int

val notimes : int
val nomult : ssrmult
val mkocc : ssrocc -> ssrdocc
val mkclr : ssrclear -> ssrdocc
val nodocc : ssrdocc
val noclr : ssrdocc

val simpltac : Ssrast.ssrsimpl -> Proof_type.tactic

val newssrcongrtac :
  int * Ssrast.ssrterm ->
  Ltac_plugin.Tacinterp.interp_sign ->
  Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma


val mk_rwarg :
  Ssrast.ssrdir * (int * Ssrast.ssrmmod) ->
  (Ssrast.ssrclear option * Ssrast.ssrocc) * Ssrmatching.rpattern option ->
  ssrwkind * Ssrast.ssrterm -> ssrrwarg

val norwmult : ssrdir * ssrmult
val norwocc : (Ssrast.ssrclear option * Ssrast.ssrocc) * Ssrmatching.rpattern option

val ssrinstancesofrule :
  Ltac_plugin.Tacinterp.interp_sign ->
  Ssrast.ssrdir ->
  Ssrast.ssrterm ->
  Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma

val ssrrewritetac :
  Ltac_plugin.Tacinterp.interp_sign ->
  ((Ssrast.ssrdir * (int * Ssrast.ssrmmod)) *
     (((Ssrast.ssrhyps option * Ssrmatching.occ) *
         Ssrmatching.rpattern option) *
        (ssrwkind * Ssrast.ssrterm)))
           list -> Proof_type.tactic

val ipat_rewrite : ssrocc -> ssrdir -> EConstr.t -> Proof_type.tactic

val unlocktac :
  Ltac_plugin.Tacinterp.interp_sign ->
  (Ssrmatching.occ * Ssrast.ssrterm) list ->
  Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma
