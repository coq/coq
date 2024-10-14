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

val simpltac : Ssrast.ssrsimpl -> unit Proofview.tactic

val newssrcongrtac :
  int * Ssrast.ssrterm ->
  Ltac_plugin.Tacinterp.interp_sign ->
  unit Proofview.tactic


val mk_rwarg :
  Ssrast.ssrdir * (int * Ssrast.ssrmmod) ->
  (Ssrast.ssrclear option * Ssrast.ssrocc) * Ssrmatching.rpattern option ->
  ssrwkind * Ssrast.ssrterm -> ssrrwarg

val norwmult : ssrdir * ssrmult
val norwocc : (Ssrast.ssrclear option * Ssrast.ssrocc) * Ssrmatching.rpattern option

val ssr_is_setoid :
  Environ.env -> Evd.evar_map -> EConstr.t -> EConstr.t array -> bool

val ssrinstancesofrule :
  Ltac_plugin.Tacinterp.interp_sign ->
  Ssrast.ssrdir ->
  Ssrast.ssrterm ->
  unit Proofview.tactic

(* map_redex (by default the identity on after) is called on the
 * redex (before) and its replacement (after). It is used to
 * "rename" binders by the under tactic *)
val ssrrewritetac :
  ?under:bool ->
  ?map_redex:(Environ.env -> Evd.evar_map ->
                 before:EConstr.t -> after:EConstr.t -> Evd.evar_map * EConstr.t) ->
  Ltac_plugin.Tacinterp.interp_sign ->
   ssrrwarg list -> unit Proofview.tactic

val ipat_rewrite : ssrocc -> ssrdir -> EConstr.t -> unit Proofview.tactic

val unlocktac :
  Ltac_plugin.Tacinterp.interp_sign ->
  (Ssrmatching.occ * Ssrast.ssrterm) list ->
  unit Proofview.tactic
