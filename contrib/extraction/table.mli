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
open Miniml

(*s Warning and Error messages. *)

val error_axiom_scheme : global_reference -> 'a
val error_axiom : global_reference -> 'a
val warning_axiom : global_reference -> unit
val error_section : unit -> 'a
val error_constant : global_reference -> 'a
val error_type_scheme : global_reference -> 'a
val error_inductive : global_reference -> 'a
val error_nb_cons : unit -> 'a

(*s AutoInline parameter *) 

val auto_inline : unit -> bool

(*s Optimize parameter *) 

val optim :  unit -> bool

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

(*s Some table-related operations *)

val add_term : kernel_name -> ml_decl -> unit
val lookup_term : kernel_name -> ml_decl

val add_type : kernel_name -> ml_schema -> unit
val lookup_type : kernel_name -> ml_schema

val add_ind : kernel_name -> ml_ind -> unit
val lookup_ind : kernel_name -> ml_ind

val add_recursors : kernel_name -> unit
val is_recursor : global_reference -> bool 

val add_record : kernel_name -> global_reference list -> unit
val find_projections : kernel_name -> global_reference list
val is_projection : global_reference -> bool 


