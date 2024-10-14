(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

let all_opaque = TransparentState.empty

open TransparentState

type reds = {
  r_beta : bool;
  r_delta : bool;
  r_const : TransparentState.t;
  r_zeta : bool;
  r_match : bool;
  r_fix : bool;
  r_cofix : bool;
}

type red_kind =
  | BETA | DELTA | MATCH | FIX | COFIX | ZETA
  | CONST of Constant.t
  | PROJ of Projection.Repr.t
  | VAR of Id.t

let fBETA = BETA
let fDELTA = DELTA
let fMATCH = MATCH
let fFIX = FIX
let fCOFIX = COFIX
let fZETA = ZETA
let fCONST kn = CONST kn
let fPROJ p = PROJ p
let fVAR id  = VAR id

let no_red = {
  r_beta = false;
  r_delta = false;
  r_const = all_opaque;
  r_zeta = false;
  r_match = false;
  r_fix = false;
  r_cofix = false;
}

let red_add red = function
  | BETA -> { red with r_beta = true }
  | DELTA -> { red with r_delta = true }
  | CONST kn ->
    let r = red.r_const in
    { red with r_const = { r with tr_cst = Cpred.add kn r.tr_cst } }
  | PROJ p ->
    let r = red.r_const in
    { red with r_const = { r with tr_prj = PRpred.add p r.tr_prj } }
  | MATCH -> { red with r_match = true }
  | FIX -> { red with r_fix = true }
  | COFIX -> { red with r_cofix = true }
  | ZETA -> { red with r_zeta = true }
  | VAR id ->
    let r = red.r_const in
    { red with r_const = { r with tr_var = Id.Pred.add id r.tr_var } }

let red_sub red = function
  | BETA -> { red with r_beta = false }
  | DELTA -> { red with r_delta = false }
  | CONST kn ->
    let r = red.r_const in
    { red with r_const = { r with tr_cst = Cpred.remove kn r.tr_cst } }
  | PROJ p ->
    let r = red.r_const in
    { red with r_const = { r with tr_prj = PRpred.remove p r.tr_prj } }
  | MATCH -> { red with r_match = false }
  | FIX -> { red with r_fix = false }
  | COFIX -> { red with r_cofix = false }
  | ZETA -> { red with r_zeta = false }
  | VAR id ->
    let r = red.r_const in
    { red with r_const = { r with tr_var = Id.Pred.remove id r.tr_var } }

let red_sub_list = List.fold_left red_sub
let red_add_list = List.fold_left red_add

let red_transparent red = red.r_const

let red_add_transparent red tr =
  { red with r_const = tr }

let mkflags = List.fold_left red_add no_red

let mkfullflags = List.fold_left red_add { no_red with r_const = TransparentState.full }

let red_set red = function
  | BETA -> red.r_beta
  | CONST kn ->
    is_transparent_constant red.r_const kn
  | PROJ p ->
    is_transparent_projection red.r_const p
  | VAR id ->
    is_transparent_variable red.r_const id
  | ZETA -> red.r_zeta
  | MATCH -> red.r_match
  | FIX -> red.r_fix
  | COFIX -> red.r_cofix
  | DELTA -> (* Used for Rel/Var defined in context *)
    red.r_delta

let red_projection red p =
  if Projection.unfolded p then true
  else red_set red (fPROJ (Projection.repr p))

let all = mkfullflags [fBETA;fDELTA;fZETA;fMATCH;fFIX;fCOFIX]
let allnolet = mkfullflags [fBETA;fDELTA;fMATCH;fFIX;fCOFIX]
let beta = mkflags [fBETA]
let betadeltazeta = mkfullflags [fBETA;fDELTA;fZETA]
let betaiota = mkflags [fBETA;fMATCH;fFIX;fCOFIX]
let betaiotazeta = mkflags [fBETA;fMATCH;fFIX;fCOFIX;fZETA]
let betazeta = mkflags [fBETA;fZETA]
let delta = mkfullflags [fDELTA]
let zeta = mkflags [fZETA]
let nored = no_red
