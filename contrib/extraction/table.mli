(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Summary
open Goptions
open Vernacinterp
open Names

(*s Set and Map over global reference *) 

module Refset : Set.S with type elt = global_reference

(*s Auxiliary functions *) 
		      
val check_constant : global_reference -> global_reference

val refs_of_vargl : vernac_arg list -> global_reference list

(*s AutoInline parameter *) 

val auto_inline : unit -> bool

(*s Optimize parameter *) 

val optim :  unit -> bool

(* Table for custom inlining *) 

val to_inline : global_reference -> bool

val to_keep : global_reference -> bool

(*s Table for direct ML extractions. *)

val is_ml_extraction : global_reference -> bool

val find_ml_extraction : global_reference -> string

val ml_extractions : unit -> Refset.t

val sorted_ml_extractions : unit -> (global_reference * string) list

