(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Lib: record of operations, backtrack, low-level sections *)

(** This module provides a general mechanism to keep a trace of all operations
   and to backtrack (undo) those operations. It provides also the section
   mechanism (at a low level; discharge is not known at this step). *)

type is_type = bool (* Module Type or just Module *)
type export_flag = Export | Import
type export = (export_flag * Libobject.open_filter) option (* None for a Module Type *)

val make_oname : Nametab.object_prefix -> Names.Id.t -> Libobject.object_name
val make_foname : Names.Id.t -> Libobject.object_name
val oname_prefix : Libobject.object_name -> Nametab.object_prefix

type node =
  | CompilingLibrary of Nametab.object_prefix
  | OpenedModule of is_type * export * Nametab.object_prefix * Summary.frozen
  | OpenedSection of Nametab.object_prefix * Summary.frozen

(** Extract the [object_prefix] component. Note that it is the prefix
   of the objects *inside* this node, eg in [Module M.] we have
   [OpenedModule] with prefix containing [M]. *)
val node_prefix : node -> Nametab.object_prefix

type library_segment = (node * Libobject.t list) list

type classified_objects = {
  substobjs : Libobject.t list;
  keepobjs : Libobject.t list;
  anticipateobjs : Libobject.t list;
}

(** {6 ... } *)
(** Low-level adding operations (does not cache) *)

val add_entry : node -> unit
val add_leaf_entry : Libobject.t -> unit

(** {6 ... } *)
(** Adding operations (which call the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : Libobject.obj -> unit

(** {6 ... } *)

(** The function [contents] gives access to the current entire segment *)

val contents : unit -> library_segment

(** {6 Functions relative to current path } *)

(** User-side names *)
val prefix : unit -> Nametab.object_prefix
val cwd : unit -> DirPath.t
val cwd_except_section : unit -> DirPath.t
val current_dirpath : bool -> DirPath.t (* false = except sections *)
val make_path : Id.t -> Libnames.full_path
val make_path_except_section : Id.t -> Libnames.full_path

(** Kernel-side names *)
val current_mp : unit -> ModPath.t
val make_kn : Id.t -> KerName.t

(** Are we inside an opened section *)
val sections_are_opened : unit -> bool
[@@ocaml.deprecated "Use Global.sections_are_opened"]
val sections_depth : unit -> int

(** Are we inside an opened module type *)
val is_module_or_modtype : unit -> bool
val is_modtype : unit -> bool
(* [is_modtype_strict] checks not only if we are in a module type, but
   if the latest module started is a module type.  *)
val is_modtype_strict : unit -> bool
val is_module : unit -> bool

(** Returns the opening node of a given name *)
val find_opening_node : Id.t -> node

(** {6 Modules and module types } *)

val start_module :
  export -> module_ident -> ModPath.t ->
  Summary.frozen -> Nametab.object_prefix

val start_modtype :
  module_ident -> ModPath.t ->
  Summary.frozen -> Nametab.object_prefix

val end_module :
  unit ->
  Nametab.object_prefix * Summary.frozen * classified_objects

val end_modtype :
  unit ->
  Nametab.object_prefix * Summary.frozen * classified_objects

(** {6 Compilation units } *)

val start_compilation : DirPath.t -> ModPath.t -> unit
val end_compilation : DirPath.t -> Nametab.object_prefix * classified_objects

(** The function [library_dp] returns the [DirPath.t] of the current
   compiling library (or [default_library]) *)
val library_dp : unit -> DirPath.t

(** Extract the library part of a name even if in a section *)
val dp_of_mp : ModPath.t -> DirPath.t
val split_modpath : ModPath.t -> DirPath.t * Id.t list
val library_part :  GlobRef.t -> DirPath.t

(** {6 Sections } *)

val open_section : Id.t -> unit
val close_section : unit -> unit

(** {6 We can get and set the state of the operations (used in [States]). } *)

type frozen

val freeze : unit -> frozen
val unfreeze : frozen -> unit

(** Keep only the libobject structure, not the objects themselves *)
val drop_objects : frozen -> frozen

val init : unit -> unit

(** {6 Section management for discharge } *)
val section_segment_of_constant : Constant.t -> Cooking.cooking_info
val section_segment_of_inductive: MutInd.t -> Cooking.cooking_info
val section_segment_of_reference : GlobRef.t -> Cooking.cooking_info

val section_instance : GlobRef.t -> Constr.t array
val is_in_section : GlobRef.t -> bool

(** {6 Discharge: decrease the section level if in the current section } *)

val discharge_proj_repr : Projection.Repr.t -> Projection.Repr.t
