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

val id_of_global : global_reference -> identifier

(*s Warning and Error messages. *)

val error_axiom_scheme : global_reference -> int -> 'a
val error_axiom : global_reference -> 'a
val warning_axiom : global_reference -> unit
val error_section : unit -> 'a
val error_constant : global_reference -> 'a
val error_fixpoint : global_reference -> 'a
val error_type_scheme : global_reference -> 'a
val error_inductive : global_reference -> 'a
val error_nb_cons : unit -> 'a
val error_module_clash : string -> 'a 
val error_unknown_module : identifier -> 'a
val error_toplevel : unit -> 'a
val error_scheme : unit -> 'a
val error_not_visible : global_reference -> 'a
val error_unqualified_name : string -> string -> 'a 

(*s utilities concerning [module_path]. *)

val current_toplevel : unit -> module_path

val is_toplevel : module_path -> bool 
val at_toplevel : module_path -> bool
val base_mp : module_path -> module_path
val prefixes_mp : module_path -> MPset.t
val is_modfile : module_path -> bool 
val modfile_of_mp : module_path -> module_path
val fst_level_module_of_mp : module_path -> module_path * label
val labels_of_mp : module_path -> module_path * label list 
val labels_of_kn : kernel_name -> module_path * label list

val is_something_opened : unit -> bool

(*s Some table-related operations *)

val add_term : kernel_name -> ml_decl -> unit
val lookup_term : kernel_name -> ml_decl

val add_type : kernel_name -> ml_schema -> unit
val lookup_type : kernel_name -> ml_schema

val add_ind : kernel_name -> ml_ind -> unit
val lookup_ind : kernel_name -> ml_ind

val add_recursors : Environ.env -> kernel_name -> unit
val is_recursor : global_reference -> bool 

val add_record : kernel_name -> int -> global_reference list -> unit
val find_projections : kernel_name -> global_reference list
val is_projection : global_reference -> bool 
val projection_arity : global_reference -> int

val add_aliases : module_path -> module_path -> unit
val long_mp : module_path -> module_path 
val long_kn : kernel_name -> kernel_name
val long_r : global_reference -> global_reference

val reset_tables : unit -> unit

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

(*s Table for user-given custom ML extractions. *)

val ugly_hack_arity_nb_args : (Environ.env -> Term.constr -> int) ref

val is_custom : global_reference -> bool
val is_inline_custom : global_reference -> bool
val find_custom : global_reference -> string
val find_type_custom : global_reference -> string list * string

(*s Extraction commands. *)

val extraction_language : lang -> unit
val extraction_inline : bool -> reference list -> unit
val print_extraction_inline : unit -> unit
val reset_extraction_inline : unit -> unit
val extract_constant_inline : 
  bool -> reference -> string list -> string -> unit
val extract_inductive : reference -> string * string list -> unit




