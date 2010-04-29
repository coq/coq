(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Names

(** Identifiers and names *)
val pr_id : identifier -> Pp.std_ppcmds
val pr_name : name -> Pp.std_ppcmds

val make_ident : string -> int option -> identifier
val repr_ident : identifier -> string * int option

val atompart_of_id : identifier -> string  (** remove trailing digits *)
val root_of_id : identifier -> identifier (** remove trailing digits, {% $ %}'{% $ %} and {% $ %}\_{% $ %} *)

val add_suffix : identifier -> string -> identifier
val add_prefix : string -> identifier -> identifier

val has_subscript    : identifier -> bool
val lift_subscript   : identifier -> identifier
val forget_subscript : identifier -> identifier

val out_name : name -> identifier

val name_fold : (identifier -> 'a -> 'a) -> name -> 'a -> 'a
val name_iter : (identifier -> unit) -> name -> unit
val name_cons : name -> identifier list -> identifier list
val name_app : (identifier -> identifier) -> name -> name
val name_fold_map : ('a -> identifier -> 'a * identifier) -> 'a -> name -> 'a * name


val pr_lab : label -> Pp.std_ppcmds

(** some preset paths *)

val default_library : dir_path

(** This is the root of the standard library of Coq *)
val coq_root : module_ident

(** This is the default root prefix for developments which doesn't
   mention a root *)
val default_root_prefix : dir_path

(** Metavariables *)
val pr_meta : Term.metavariable -> Pp.std_ppcmds
val string_of_meta : Term.metavariable -> string
