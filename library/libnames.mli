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
open Identifier
open Names
(*i*)

(*s [path_kind] is currently degenerated, [FW] is not used *)
type path_kind = CCI | FW | OBJ

(* parsing and printing of path kinds *)
val string_of_kind : path_kind -> string
val kind_of_string : string -> path_kind


(*s Section paths are {\em absolute} names *)
type section_path

(* Constructors of [section_path] *)
val make_path : dir_path -> identifier -> path_kind -> section_path

(* Destructors of [section_path] *)
val repr_path : section_path -> dir_path * identifier * path_kind
val dirpath : section_path -> dir_path
val basename : section_path -> identifier
val kind_of_path : section_path -> path_kind

val sp_of_wd : dir_path -> section_path
val wd_of_sp : section_path -> dir_path

(* Parsing and printing of section path as ["coq_root.module.id"] *)
val path_of_string : string -> section_path
val string_of_path : section_path -> string
val pr_sp : section_path -> std_ppcmds
val dirpath_of_string : string -> dir_path

(*i
val string_of_path_mind : section_path -> identifier -> string
val coerce_path : path_kind -> section_path -> section_path
val fwsp_of : section_path -> section_path
val ccisp_of : section_path -> section_path
val objsp_of : section_path -> section_path
val fwsp_of_ccisp : section_path -> section_path
val ccisp_of_fwsp : section_path -> section_path
val append_to_path : section_path -> string -> section_path

val sp_gt : section_path * section_path -> bool
i*)
val sp_ord : section_path -> section_path -> int

(* [is_dirpath_prefix p1 p2=true] if [p1] is a prefix of or is equal to [p2] *)
val dirpath_prefix_of : dir_path -> dir_path -> bool
(*i
module Spset : Set.S with type elt = section_path
i*)
module Spmap : Map.S with type key = section_path


(*s A module name identifier *)

type module_ident = identifier

module ModIdmap : Map.S with type key = module_ident


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
