(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Environ
open Symbol
open Names

(* if d=Pos, say if constant [kn] occurs positively in [c]
        Neg                              negatively
        Nul                       does not occur           *)
val occur_const : env -> symbol -> delta -> constr -> bool

(* if d=Pos, say if inductive [kn] occurs positively in [c]
        Neg                               negatively
        Nul                        does not occur           *)
val occur_mind : env -> mutual_inductive -> delta -> constr -> bool
