(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Coq interface to the Whelp query engine developed at
   the University of Bologna *)

open Names
open Term
open Topconstr
open Environ

type whelp_request =
  | Locate of string
  | Elim of inductive
  | Constr of string * constr

val whelp : whelp_request -> unit
