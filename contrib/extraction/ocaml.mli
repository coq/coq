(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Production of Ocaml syntax. We export both a functor to be used for 
    extraction in the Coq toplevel and a module [Pp] to be used for
    production of Ocaml files. *)

open Miniml

module Make : functor(P : Mlpp_param) -> Mlpp

module Pp : Mlpp

