(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s This module declares the extraction commands. *)

open Names
open Libnames

val extraction : reference -> unit
val extraction_rec : reference list -> unit
val extraction_file : string -> reference list -> unit
val extraction_module : reference -> unit
val extraction_library : identifier -> unit
val recursive_extraction_library : identifier -> unit
