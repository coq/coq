(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* The CoqIde main module. The following function [start] will parse the
   command line, initialize the load path, load the input 
   state, load the files given on the command line, load the ressource file,
   produce the output state if any, and finally will launch the interface. *)

val start : unit -> unit
