(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
(*open Identifier*)
open Names
(*i*)

(*s Global reference is a kernel side type for all references together *)
type global_reference =
  | VarRef of variable
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

(* subst_global_ref : substitution -> global_reference -> global_reference *)

(* dirpaths *)
val pr_dirpath : dir_path -> Pp.std_ppcmds
val empty_dirpath : dir_path

val dirpath_of_string : string -> dir_path

(* Give the immediate prefix of a [dir_path] *)
val dirpath_prefix : dir_path -> dir_path 

(* Give the immediate prefix and basename of a [dir_path] *)
val split_dirpath : dir_path -> dir_path * identifier

val extend_dirpath : dir_path -> module_ident -> dir_path
val add_dirpath_prefix : module_ident -> dir_path -> dir_path

val extract_dirpath_prefix : int -> dir_path -> dir_path
val is_dirpath_prefix_of : dir_path -> dir_path -> bool

(*s Section paths are {\em absolute} names *)
type section_path

(* Constructors of [section_path] *)
val make_path : dir_path -> identifier -> section_path

(* Destructors of [section_path] *)
val repr_path : section_path -> dir_path * identifier
val dirpath : section_path -> dir_path
val basename : section_path -> identifier

(* Parsing and printing of section path as ["coq_root.module.id"] *)
val path_of_string : string -> section_path
val string_of_path : section_path -> string
val pr_sp : section_path -> std_ppcmds

module Sppred : Predicate.S with type elt = section_path
module Spmap  : Map.S with type key = section_path

val restrict_path : int -> section_path -> section_path


(*s Temporary function to brutally form kernel names from section paths *)

val encode_kn : dir_path -> identifier -> kernel_name
val decode_kn : kernel_name -> dir_path * identifier


(*s A [qualid] is a partially qualified ident; it includes fully
    qualified names (= absolute names) and all intermediate partial
    qualifications of absolute names, including single identifiers *)
type qualid

val make_qualid : dir_path -> identifier -> qualid
val repr_qualid : qualid -> dir_path * identifier

val string_of_qualid : qualid -> string
val pr_qualid : qualid -> std_ppcmds

(* Turns an absolute name into a qualified name denoting the same name *)
val qualid_of_sp : section_path -> qualid

val qualid_of_dirpath : dir_path -> qualid

val make_short_qualid : identifier -> qualid
