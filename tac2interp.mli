(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genarg
open Names
open Tac2expr

exception LtacError of KerName.t * valexpr

type environment = valexpr Id.Map.t

val empty_environment : environment

val interp : environment -> glb_tacexpr -> valexpr Proofview.tactic
