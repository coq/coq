(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Names
open Libnames

(*s Warning and Error messages. *)

val error_section : unit -> 'a

val error_axiom_scheme : kernel_name -> 'a

val error_axiom : kernel_name -> 'a

val warning_axiom : kernel_name -> unit

(*s AutoInline parameter *) 

val auto_inline : unit -> bool

(*s Optimize parameter *) 

val optim :  unit -> bool

(*s Set and Map over global reference *) 

module Refset : Set.S with type elt = global_reference
module Refmap : Map.S with type key = global_reference

(*s Target language. *)

type lang = Ocaml | Haskell | Scheme | Toplevel

val lang : unit -> lang 

(*s Table for custom inlining *) 

val to_inline : global_reference -> bool

val to_keep : global_reference -> bool

(*s Table for direct ML extractions. *)

val is_ml_extraction : global_reference -> bool

val find_ml_extraction : global_reference -> string

val ml_extractions : unit -> Refset.t

val ml_type_extractions : unit -> (global_reference * string) list

val ml_term_extractions : unit -> (global_reference * string) list

(*s Extraction commands. *)

val extraction_language : lang -> unit

val extraction_inline : bool -> reference list -> unit

val print_extraction_inline : unit -> unit

val reset_extraction_inline : unit -> unit

val extract_constant_inline : bool -> reference -> string -> unit

val extract_inductive : reference -> string * string list -> unit


