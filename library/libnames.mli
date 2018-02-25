(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

(** {6 Dirpaths } *)
val dirpath_of_string : string -> DirPath.t

val pr_dirpath : DirPath.t -> Pp.t
[@@ocaml.deprecated "Alias for DirPath.print"]

val string_of_dirpath : DirPath.t -> string
[@@ocaml.deprecated "Alias for DirPath.to_string"]

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

module Dirset : Set.S with type elt = DirPath.t
module Dirmap : Map.ExtS with type key = DirPath.t and module Set := Dirset

(** {6 Full paths are {e absolute} paths of declarations } *)
type full_path

val eq_full_path : full_path -> full_path -> bool

(** Constructors of [full_path] *)
val make_path : DirPath.t -> Id.t -> full_path

(** Destructors of [full_path] *)
val repr_path : full_path -> DirPath.t * Id.t
val dirpath : full_path -> DirPath.t
val basename : full_path -> Id.t

(** Parsing and printing of section path as ["coq_root.module.id"] *)
val path_of_string : string -> full_path
val string_of_path : full_path -> string
val pr_path : full_path -> Pp.t

module Spmap  : CSig.MapS with type key = full_path

val restrict_path : int -> full_path -> full_path

(** {6 ... } *)
(** A [qualid] is a partially qualified ident; it includes fully
    qualified names (= absolute names) and all intermediate partial
    qualifications of absolute names, including single identifiers.
    The [qualid] are used to access the name table. *)

type qualid

val make_qualid : DirPath.t -> Id.t -> qualid
val repr_qualid : qualid -> DirPath.t * Id.t

val qualid_eq : qualid -> qualid -> bool

val pr_qualid : qualid -> Pp.t
val string_of_qualid : qualid -> string
val qualid_of_string : string -> qualid

(** Turns an absolute name, a dirpath, or an Id.t into a
   qualified name denoting the same name *)

val qualid_of_path : full_path -> qualid
val qualid_of_dirpath : DirPath.t -> qualid
val qualid_of_ident : Id.t -> qualid

(** Both names are passed to objects: a "semantic" [kernel_name], which
   can be substituted and a "syntactic" [full_path] which can be printed
*)

type object_name = full_path * KerName.t

(** Object prefix morally contains the "prefix" naming of an object to
   be stored by [library], where [obj_dir] is the "absolute" path,
   [obj_mp] is the current "module" prefix and [obj_sec] is the
   "section" prefix.

    Thus, for an object living inside [Module A. Section B.] the
   prefix would be:

    [ { obj_dir = "A.B"; obj_mp = "A"; obj_sec = "B" } ]

    Note that both [obj_dir] and [obj_sec] are "paths" that is to say,
   as opposed to [obj_mp] which is a single module name.

 *)
type object_prefix = {
  obj_dir : DirPath.t;
  obj_mp  : ModPath.t;
  obj_sec : DirPath.t;
}

val eq_op : object_prefix -> object_prefix -> bool

val make_oname : object_prefix -> Id.t -> object_name

(** to this type are mapped [DirPath.t]'s in the nametab *)
type global_dir_reference =
  | DirOpenModule of object_prefix
  | DirOpenModtype of object_prefix
  | DirOpenSection of object_prefix
  | DirModule of object_prefix
  | DirClosedSection of DirPath.t
      (** this won't last long I hope! *)

val eq_global_dir_reference : 
  global_dir_reference -> global_dir_reference -> bool

(** {6 ... } *)
(** A [reference] is the user-level notion of name. It denotes either a
    global name (referred either by a qualified name or by a single
    name) or a variable *)

type reference_r =
  | Qualid of qualid
  | Ident of Id.t
type reference = reference_r CAst.t

val eq_reference : reference -> reference -> bool
val qualid_of_reference : reference -> qualid CAst.t
val string_of_reference : reference -> string
val pr_reference : reference -> Pp.t
val join_reference : reference -> reference -> reference

(** some preset paths *)
val default_library : DirPath.t

(** This is the root of the standard library of Coq *)
val coq_root : module_ident (** "Coq" *)
val coq_string : string (** "Coq" *)

(** This is the default root prefix for developments which doesn't
   mention a root *)
val default_root_prefix : DirPath.t

(** Deprecated synonyms *)
val make_short_qualid : Id.t -> qualid (** = qualid_of_ident *)
[@@ocaml.deprecated "Alias for qualid_of_ident"]

val qualid_of_sp : full_path -> qualid (** = qualid_of_path *)
[@@ocaml.deprecated "Alias for qualid_of_sp"]
