(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Extraction from Coq terms to Miniml. *)

open Miniml
open Nametab

(*s ML declaration corresponding to a Coq reference. *)

val extract_declaration : global_reference -> ml_decl

(*s Check whether a global reference corresponds to a logical inductive. *)

val decl_is_logical_ind : global_reference -> bool

(*s Check if a global reference corresponds to the constructor of 
  a singleton inductive. *)

val decl_is_singleton : global_reference -> bool

