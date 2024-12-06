(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** {6 Dirpaths } *)
val dirpath_of_string : string -> DirPath.t

(** Pop the suffix of a [DirPath.t]. Raises a [Failure] for an empty path *)
val pop_dirpath : DirPath.t -> DirPath.t

(** Pop the suffix n times *)
val pop_dirpath_n : int -> DirPath.t -> DirPath.t

(** Immediate prefix and basename of a [DirPath.t]. May raise [Failure] *)
val split_dirpath : DirPath.t -> DirPath.t * Id.t

val add_dirpath_suffix : DirPath.t -> module_ident -> DirPath.t
val add_dirpath_prefix : module_ident -> DirPath.t -> DirPath.t

val chop_dirpath : int -> DirPath.t -> DirPath.t * DirPath.t
val append_dirpath : DirPath.t -> DirPath.t -> DirPath.t

val drop_dirpath_prefix : DirPath.t -> DirPath.t -> DirPath.t
val is_dirpath_prefix_of : DirPath.t -> DirPath.t -> bool

val is_dirpath_suffix_of : DirPath.t -> DirPath.t -> bool

(** {6 Full paths are {e absolute} paths of declarations } *)
type full_path

val eq_full_path : full_path -> full_path -> bool

(** Constructors of [full_path] *)
val make_path : DirPath.t -> Id.t -> full_path

(** Destructors of [full_path] *)
val repr_path : full_path -> DirPath.t * Id.t
val dirpath : full_path -> DirPath.t
val basename : full_path -> Id.t
val full_path_is_ident : full_path -> bool

(** Parsing and printing of section path as ["root.module.id"] *)
val path_of_string : string -> full_path
val string_of_path : full_path -> string
val pr_path : full_path -> Pp.t

module Spmap  : CSig.MapS with type key = full_path

(** {6 ... } *)
(** A [qualid] is a partially qualified ident; it includes fully
    qualified names (= absolute names) and all intermediate partial
    qualifications of absolute names, including single identifiers.
    The [qualid] are used to access the name table. *)

type qualid_r
type qualid = qualid_r CAst.t

val make_qualid : ?loc:Loc.t -> DirPath.t -> Id.t -> qualid
val repr_qualid : qualid -> DirPath.t * Id.t

val qualid_eq : qualid -> qualid -> bool
val is_qualid_suffix_of_full_path : qualid -> full_path -> bool

val pr_qualid : qualid -> Pp.t
val string_of_qualid : qualid -> string
val qualid_of_string : ?loc:Loc.t -> string -> qualid

(** Turns an absolute name, a dirpath, or an Id.t into a
   qualified name denoting the same name *)

val qualid_of_path : ?loc:Loc.t -> full_path -> qualid
val qualid_of_dirpath : ?loc:Loc.t -> DirPath.t -> qualid
val qualid_of_ident : ?loc:Loc.t -> Id.t -> qualid
val qualid_of_lident : lident -> qualid

val qualid_is_ident : qualid -> bool
val qualid_path : qualid -> DirPath.t
val qualid_basename : qualid -> Id.t

val idset_mem_qualid : qualid -> Id.Set.t -> bool
(** false when the qualid is not an ident *)

(** {6 ... } *)

(** This is the root of the rocq-core library *)
val rocq_init_root : module_ident (* "Corelib" *)
val rocq_init_string : string (* "Corelib" *)

(** This is the default root prefix for developments which doesn't
   mention a root *)
val default_root_prefix : DirPath.t
