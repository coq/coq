(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s This module declares the extraction commands. *)

open Util
open Names
open Nametab

val extraction : Genarg.constr_ast -> unit
val extraction_rec : qualid located list -> unit
val extraction_file : string -> qualid located list -> unit
val extraction_module : identifier -> unit
val recursive_extraction_module : identifier -> unit
