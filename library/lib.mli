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

type 'summary node =
  | CompilingLibrary of Nametab.object_prefix
  | OpenedModule of is_type * export * Nametab.object_prefix * 'summary
  | OpenedSection of Nametab.object_prefix * 'summary

(** Extract the [object_prefix] component. Note that it is the prefix
   of the objects *inside* this node, eg in [Module M.] we have
   [OpenedModule] with prefix containing [M]. *)
val node_prefix : 'summary node -> Nametab.object_prefix

type 'summary library_segment = ('summary node * Libobject.t list) list

(** {6 ... } *)
(** Adding operations (which call the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : Libobject.obj -> unit

val add_discharged_leaf : Libobject.discharged_obj -> unit

(** {6 ... } *)

(** The function [contents] gives access to the current entire segment *)

val contents : unit -> Summary.Interp.frozen library_segment

(** {6 Functions relative to current path } *)

(** User-side names

    [cwd()] is [(prefix()).obj_dir]
    [current_mp()] is [(prefix()).obj_mp]

    Inside a library A.B module M section S, we have
    - library_dp = A.B
    - cwd = A.B.M.S
    - cwd_except_section = A.B.M
    - current_dirpath true = M.S
    - current_dirpath false = S
    - current_mp = MPdot(MPfile A.B, M)

    make_path (resp make_path_except_section) uses cwd (resp cwd_except_section)
    make_kn uses current_mp
*)
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
val sections_depth : unit -> int

(** Are we inside an opened module type *)
val is_module_or_modtype : unit -> bool
val is_modtype : unit -> bool
(* [is_modtype_strict] checks not only if we are in a module type, but
   if the latest module started is a module type.  *)
val is_modtype_strict : unit -> bool
val is_module : unit -> bool

type discharged_item =
  | DischargedExport of Libobject.ExportObj.t
  | DischargedLeaf of Libobject.discharged_obj

type classified_objects = {
  substobjs : Libobject.t list;
  keepobjs : Libobject.t list;
  escapeobjs : Libobject.t list;
  anticipateobjs : Libobject.t list;
}

(** The [StagedLibS] abstraction describes operations and traversal for Lib at a
    given stage. *)
module type StagedLibS = sig

  type summary

  (** Returns the opening node of a given name *)
  val find_opening_node : ?loc:Loc.t -> Id.t -> summary node

  val add_entry : summary node -> unit
  val add_leaf_entry : Libobject.t -> unit

  (** {6 Sections } *)
  val open_section : Id.t -> unit

  (** [close_section] needs to redo Export, so the complete
      implementation needs to involve [Declaremods]. *)
  val close_section : unit -> discharged_item list

  (** {6 Modules and module types } *)

  val start_module :
    export -> module_ident -> ModPath.t ->
    summary -> Nametab.object_prefix

  val start_modtype :
    module_ident -> ModPath.t ->
    summary -> Nametab.object_prefix

  val end_module :
    unit ->
    Nametab.object_prefix * summary * classified_objects

  val end_modtype :
    unit ->
    Nametab.object_prefix * summary * classified_objects

  type frozen

  val freeze : unit -> frozen
  val unfreeze : frozen -> unit
  val init : unit -> unit

  (** Keep only the libobject structure, not the objects themselves *)
  val drop_objects : frozen -> frozen

  val declare_info : Library_info.t -> unit

end

(** We provide two instances of [StagedLibS], corresponding to the Synterp and
    Interp stages. *)

module Synterp : StagedLibS with type summary = Summary.Synterp.frozen
module Interp : StagedLibS with type summary = Summary.Interp.frozen

(** {6 Compilation units } *)

val start_compilation : DirPath.t -> ModPath.t -> unit

type compilation_result = {
  info : Library_info.t;
  synterp_objects : classified_objects;
  interp_objects : classified_objects;
}

(** Finalize the compilation of a library. *)
val end_compilation : DirPath.t -> compilation_result

(** The function [library_dp] returns the [DirPath.t] of the current
   compiling library (or [default_library]) *)
val library_dp : unit -> DirPath.t

(** Extract the library part of a name even if in a section *)
val split_modpath : ModPath.t -> DirPath.t * Id.t list
val library_part :  GlobRef.t -> DirPath.t

(** {6 Section management for discharge } *)
val section_segment_of_constant : Constant.t -> Cooking.cooking_info
val section_segment_of_inductive: MutInd.t -> Cooking.cooking_info
val section_segment_of_reference : GlobRef.t -> Cooking.cooking_info

val section_instance : GlobRef.t -> Constr.t array
val is_in_section : GlobRef.t -> bool

(** {6 Discharge: decrease the section level if in the current section } *)

(** [discharge_proj_repr p] discharges projection [p] if the associated record
    was defined in the current section. If that is not the case, it returns [p]
    unchanged. *)
val discharge_proj_repr : Projection.Repr.t -> Projection.Repr.t

(** Compatibility layer *)

(** This also does init_summaries *)
val init : unit -> unit
