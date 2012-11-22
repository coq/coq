(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Loc
open Names

(** {6 Dirpaths } *)
val pr_dirpath : dir_path -> Pp.std_ppcmds

val dirpath_of_string : string -> dir_path
val string_of_dirpath : dir_path -> string

(** Pop the suffix of a [dir_path] *)
val pop_dirpath : dir_path -> dir_path

(** Pop the suffix n times *)
val pop_dirpath_n : int -> dir_path -> dir_path

(** Give the immediate prefix and basename of a [dir_path] *)
val split_dirpath : dir_path -> dir_path * identifier

val add_dirpath_suffix : dir_path -> module_ident -> dir_path
val add_dirpath_prefix : module_ident -> dir_path -> dir_path

val chop_dirpath : int -> dir_path -> dir_path * dir_path
val append_dirpath : dir_path -> dir_path -> dir_path

val drop_dirpath_prefix : dir_path -> dir_path -> dir_path
val is_dirpath_prefix_of : dir_path -> dir_path -> bool

module Dirset : Set.S with type elt = dir_path
module Dirmap : Map.S with type key = dir_path

(** {6 Full paths are {e absolute} paths of declarations } *)
type full_path

val eq_full_path : full_path -> full_path -> bool

(** Constructors of [full_path] *)
val make_path : dir_path -> identifier -> full_path

(** Destructors of [full_path] *)
val repr_path : full_path -> dir_path * identifier
val dirpath : full_path -> dir_path
val basename : full_path -> identifier

(** Parsing and printing of section path as ["coq_root.module.id"] *)
val path_of_string : string -> full_path
val string_of_path : full_path -> string
val pr_path : full_path -> std_ppcmds

module Spmap  : Map.S with type key = full_path

val restrict_path : int -> full_path -> full_path

(** {6 ... } *)
(** A [qualid] is a partially qualified ident; it includes fully
    qualified names (= absolute names) and all intermediate partial
    qualifications of absolute names, including single identifiers.
    The [qualid] are used to access the name table. *)

type qualid

val make_qualid : dir_path -> identifier -> qualid
val repr_qualid : qualid -> dir_path * identifier

val qualid_eq : qualid -> qualid -> bool

val pr_qualid : qualid -> std_ppcmds
val string_of_qualid : qualid -> string
val qualid_of_string : string -> qualid

(** Turns an absolute name, a dirpath, or an identifier into a
   qualified name denoting the same name *)

val qualid_of_path : full_path -> qualid
val qualid_of_dirpath : dir_path -> qualid
val qualid_of_ident : identifier -> qualid

(** Both names are passed to objects: a "semantic" [kernel_name], which
   can be substituted and a "syntactic" [full_path] which can be printed
*)

type object_name = full_path * kernel_name

type object_prefix = dir_path * (module_path * dir_path)

val eq_op : object_prefix -> object_prefix -> bool

val make_oname : object_prefix -> identifier -> object_name

(** to this type are mapped [dir_path]'s in the nametab *)
type global_dir_reference =
  | DirOpenModule of object_prefix
  | DirOpenModtype of object_prefix
  | DirOpenSection of object_prefix
  | DirModule of object_prefix
  | DirClosedSection of dir_path
      (** this won't last long I hope! *)

val eq_global_dir_reference : 
  global_dir_reference -> global_dir_reference -> bool

(** {6 ... } *)
(** A [reference] is the user-level notion of name. It denotes either a
    global name (referred either by a qualified name or by a single
    name) or a variable *)

type reference =
  | Qualid of qualid located
  | Ident of identifier located

val eq_reference : reference -> reference -> bool
val qualid_of_reference : reference -> qualid located
val string_of_reference : reference -> string
val pr_reference : reference -> std_ppcmds
val loc_of_reference : reference -> Loc.t

(** Deprecated synonyms *)

val make_short_qualid : identifier -> qualid (** = qualid_of_ident *)
val qualid_of_sp : full_path -> qualid (** = qualid_of_path *)
