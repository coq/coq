(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Topconstr
open Rawterm
open Nametab
open Libnames
(*i*)

(* Syntactic definitions. *)

type syndef_interpretation = (identifier * subscopes) list * aconstr

val declare_syntactic_definition : bool -> identifier -> bool ->
  syndef_interpretation -> unit

val search_syntactic_definition : kernel_name -> syndef_interpretation
