(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Some utility functions to be reused in module [Haskell]. *)

open Pp
open Miniml
open Names

val keywords : Idset.t

val preamble : extraction_params -> Idset.t -> bool * bool * bool -> std_ppcmds

module Make : functor(P : Mlpp_param) -> Mlpp





