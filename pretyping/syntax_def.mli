(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Libnames
open Rawterm
(*i*)

(* Syntactic definitions. *)

val declare_syntactic_definition : identifier -> rawconstr -> unit

val search_syntactic_definition : section_path -> rawconstr

val locate_syntactic_definition : qualid -> section_path


