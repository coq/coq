(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Vernacinterp
open Names
open Nametab

(*s AutoInline parameter *) 

val auto_inline : unit -> bool

(*s Optimize parameter *) 

val optim :  unit -> bool

(*s Set and Map over global reference *) 

module Refset : Set.S with type elt = global_reference

(*s Auxiliary functions *) 
		      
val check_constant : global_reference -> global_reference

(*val refs_of_vargl : Extend.vernac_arg list -> global_reference list*)

(*s Target language. *)

type lang = Ocaml | Haskell | Toplevel

val lang : unit -> lang 

(*s Table for custom inlining *) 

val to_inline : global_reference -> bool

val to_keep : global_reference -> bool

(*s Table for direct ML extractions. *)

val is_ml_extraction : global_reference -> bool

val find_ml_extraction : global_reference -> string

val ml_extractions : unit -> Refset.t

val sorted_ml_extractions : unit -> (global_reference * string) list

(*s Extraction commands. *)

open Util

val extraction_language : lang -> unit

val extraction_inline : bool -> qualid located list -> unit

val print_extraction_inline : unit -> unit

val reset_extraction_inline : unit -> unit

val extract_constant_inline : bool -> qualid located -> string -> unit

val extract_inductive : qualid located -> string * string list -> unit
