(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Term
open Environ

(* Identifiers and names *)
val wildcard : identifier

val make_ident : string -> int option -> identifier
val repr_ident : identifier -> string * int option

val atompart_of_id : identifier -> string

val add_suffix : identifier -> string -> identifier
val add_prefix : string -> identifier -> identifier

val lift_ident           : identifier -> identifier
val next_ident_away      : identifier -> identifier list -> identifier
val next_ident_away_from : identifier -> identifier list -> identifier

val next_name_away : name -> identifier list -> identifier
val next_name_away_with_default :
  string -> name -> identifier list -> identifier

val out_name : name -> identifier

(* Section and module mechanism: dealinng with dir paths *)
val empty_dirpath : dir_path
val default_module : dir_path

(* This is the root of the standard library of Coq *)
val coq_root : module_ident

(* This is the default root prefix for developments which doesn't
   mention a root *)
val default_root_prefix : dir_path


val dirpath_of_string : string -> dir_path
val path_of_string : string -> section_path

val path_of_constructor : env -> constructor -> section_path
val path_of_inductive   : env -> inductive -> section_path


val dirpath : section_path -> dir_path
val basename : section_path -> identifier

(* Give the immediate prefix of a [dir_path] *)
val dirpath_prefix : dir_path -> dir_path 

(* Give the immediate prefix and basename of a [dir_path] *)
val split_dirpath : dir_path -> dir_path * identifier

val extend_dirpath : dir_path -> module_ident -> dir_path
val add_dirpath_prefix : module_ident -> dir_path -> dir_path

val extract_dirpath_prefix : int -> dir_path -> dir_path
val is_dirpath_prefix_of : dir_path -> dir_path -> bool

val restrict_path : int -> section_path -> section_path

