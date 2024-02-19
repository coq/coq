(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

type reds = { flags : int; ts : TransparentState.t }

type red_kind =
  | FLAG of int
  | CONST of Constant.t
  | PROJ of Projection.Repr.t
  | VAR of Id.t

let fBETA  = FLAG 0b000001
let fDELTA = FLAG 0b000010
let fMATCH = FLAG 0b000100
let fFIX   = FLAG 0b001000
let fCOFIX = FLAG 0b010000
let fZETA  = FLAG 0b100000
let fCONST kn  = CONST kn
let fPROJ p = PROJ p
let fVAR id  = VAR id

let no_red = {flags = 0; ts = all_opaque}

let red_add ({flags; ts} as red) = function
  | FLAG f -> {red with flags = flags lor f}
  | CONST kn -> {red with ts = {ts with tr_cst = Cpred.add kn ts.tr_cst}}
  | PROJ p -> {red with ts = {ts with tr_prj = PRpred.add p ts.tr_prj}}
  | VAR id -> {red with ts = {ts with tr_var = Id.Pred.add id ts.tr_var}}

let red_sub ({flags; ts} as red) = function
  | FLAG f -> {red with flags = flags land (0b111111 lxor f)}
  | CONST kn -> {red with ts = {ts with tr_cst = Cpred.remove kn ts.tr_cst}}
  | PROJ p -> {red with ts = {ts with tr_prj = PRpred.remove p ts.tr_prj}}
  | VAR id -> { red with ts = {ts with tr_var = Id.Pred.remove id ts.tr_var}}

let red_sub_list = List.fold_left red_sub
let red_add_list = List.fold_left red_add

let red_transparent red = red.ts

let red_add_transparent red ts = { red with ts }

let mkflags = List.fold_left red_add no_red

let mkfullflags = List.fold_left red_add { no_red with ts = TransparentState.full }


let red_set red = function
  | FLAG f -> red.flags land f != 0
  | CONST kn -> is_transparent_constant red.ts kn
  | PROJ p -> is_transparent_projection red.ts p
  | VAR id -> is_transparent_variable red.ts id

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
