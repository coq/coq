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
(*i*)

(*s Identifiers *)

type identifier
type name = Name of identifier | Anonymous

(* Constructor of an identifier;
   [make_ident] builds an identifier from a string and an optional index; if
   the string ends by a digit, a ["_"] is inserted *)
val make_ident : string -> int option -> identifier

(* Some destructors of an identifier *)
val atompart_of_id : identifier -> string
val first_char : identifier -> string
val index_of_id : identifier -> int option

(* Parsing and printing of identifiers *)
val string_of_id : identifier -> string
val id_of_string : string -> identifier
val pr_id : identifier -> std_ppcmds

(* This is the identifier ["_"] *)
val wildcard : identifier

(* Deriving ident from other idents *)
val add_suffix : identifier -> string -> identifier
val add_prefix : string -> identifier -> identifier

(* Identifiers sets and maps *)
module Idset  : Set.S with type elt = identifier
module Idpred : Predicate.S with type elt = identifier
module Idmap  : Map.S with type key = identifier

val lift_ident : identifier -> identifier
val next_ident_away_from : identifier -> identifier list -> identifier
val next_ident_away : identifier -> identifier list -> identifier
val next_name_away : name -> identifier list -> identifier
val next_name_away_with_default : 
  string -> name -> identifier list -> identifier

(* [out_name na] raises an anomaly if [na] is [Anonymous] *)
val out_name : name -> identifier

(*s [path_kind] is currently degenerated, [FW] is not used *)
type path_kind = CCI | FW | OBJ

(* parsing and printing of path kinds *)
val string_of_kind : path_kind -> string
val kind_of_string : string -> path_kind

(*s Directory paths = section names paths *)
type module_ident = identifier
type dir_path = module_ident list

module ModIdmap : Map.S with type key = module_ident

val make_dirpath : module_ident list -> dir_path
val repr_dirpath : dir_path -> module_ident list

(* Give the immediate prefix of a [dir_path] *)
val dirpath_prefix : dir_path -> dir_path 

(* Give the immediate prefix and basename of a [dir_path] *)
val split_dirpath : dir_path -> dir_path * identifier

(* Printing of directory paths as ["coq_root.module.submodule"] *)
val string_of_dirpath : dir_path -> string
val pr_dirpath : dir_path -> std_ppcmds


(*s Section paths are {\em absolute} names *)
type section_path

(* Constructors of [section_path] *)
val make_path : dir_path -> identifier -> path_kind -> section_path

(* Destructors of [section_path] *)
val repr_path : section_path -> dir_path * identifier * path_kind
val dirpath : section_path -> dir_path
val basename : section_path -> identifier
val kind_of_path : section_path -> path_kind

val sp_of_wd : module_ident list -> section_path
val wd_of_sp : section_path -> module_ident list

(* Parsing and printing of section path as ["coq_root.module.id"] *)
val path_of_string : string -> section_path
val string_of_path : section_path -> string
val pr_sp : section_path -> std_ppcmds
val dirpath_of_string : string -> dir_path

val sp_ord : section_path -> section_path -> int

(* [is_dirpath_prefix p1 p2=true] if [p1] is a prefix of or is equal to [p2] *)
val is_dirpath_prefix_of : dir_path -> dir_path -> bool

module Spset  : Set.S with type elt = section_path
module Sppred : Predicate.S with type elt = section_path
module Spmap  : Map.S with type key = section_path

(*s Specific paths for declarations *)
type variable_path = section_path
type constant_path = section_path
type inductive_path = section_path * int
type constructor_path = inductive_path * int
type mutual_inductive_path = section_path

(* Hash-consing *)
val hcons_names : unit ->
  (section_path -> section_path) * (section_path -> section_path) *
  (name -> name) * (identifier -> identifier) * (string -> string)
