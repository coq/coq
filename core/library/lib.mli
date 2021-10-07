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
type export = bool option (* None for a Module Type *)

val make_oname : Nametab.object_prefix -> Names.Id.t -> Libobject.object_name
val make_foname : Names.Id.t -> Libnames.full_path * Names.KerName.t

type node =
  | Leaf of Libobject.t
  | CompilingLibrary of Nametab.object_prefix
  | OpenedModule of is_type * export * Nametab.object_prefix * Summary.frozen
  | OpenedSection of Nametab.object_prefix * Summary.frozen

type library_segment = (Libobject.object_name * node) list

type lib_atomic_objects = (Id.t * Libobject.obj) list
type lib_objects = (Id.t * Libobject.t) list

(** {6 Object iteration functions. } *)

val open_atomic_objects : Libobject.open_filter
  -> int -> Nametab.object_prefix -> lib_atomic_objects -> unit
val load_atomic_objects : int -> Nametab.object_prefix -> lib_atomic_objects -> unit
val subst_atomic_objects : Mod_subst.substitution -> lib_atomic_objects -> lib_atomic_objects
(*val load_and_subst_objects : int -> Libnames.Nametab.object_prefix -> Mod_subst.substitution -> lib_objects -> lib_objects*)

(** [classify_segment seg] verifies that there are no OpenedThings,
   clears ClosedSections and FrozenStates and divides Leafs according
   to their answers to the [classify_object] function in three groups:
   [Substitute], [Keep], [Anticipate] respectively.  The order of each
   returned list is the same as in the input list. *)
val classify_segment :
  library_segment -> lib_objects * lib_objects * Libobject.t list

(** [segment_of_objects prefix objs] forms a list of Leafs *)
val segment_of_objects :
  Nametab.object_prefix -> lib_objects -> library_segment

(** {6 ... } *)
(** Low-level adding operations *)

val add_entry : Libobject.object_name -> node -> unit
val add_anonymous_entry : node -> unit

(** {6 ... } *)
(** Adding operations (which call the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : Id.t -> Libobject.obj -> Libobject.object_name
val add_anonymous_leaf : ?cache_first:bool -> Libobject.obj -> unit

(** {6 ... } *)

(** The function [contents] gives access to the current entire segment *)

val contents : unit -> library_segment

(** The function [contents_after] returns the current library segment,
  starting from a given section path. *)

val contents_after : Libobject.object_name -> library_segment

(** {6 Functions relative to current path } *)

(** User-side names *)
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
val current_mod_id : unit -> module_ident

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
  Libobject.object_name * Nametab.object_prefix *
    Summary.frozen * library_segment

val end_modtype :
  unit ->
  Libobject.object_name * Nametab.object_prefix *
    Summary.frozen * library_segment

(** {6 Compilation units } *)

val start_compilation : DirPath.t -> ModPath.t -> unit
val end_compilation_checks : DirPath.t -> Libobject.object_name
val end_compilation :
  Libobject.object_name-> Nametab.object_prefix * library_segment

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
val section_segment_of_constant : Constant.t -> Declarations.abstr_info
val section_segment_of_mutual_inductive: MutInd.t -> Declarations.abstr_info
val section_segment_of_reference : GlobRef.t -> Declarations.abstr_info

val variable_section_segment_of_reference : GlobRef.t -> Constr.named_context

val section_instance : GlobRef.t -> Univ.Instance.t * Id.t array
val is_in_section : GlobRef.t -> bool

val replacement_context : unit -> Declarations.work_list

(** {6 Discharge: decrease the section level if in the current section } *)

(* XXX Why can't we use the kernel functions ? *)

val discharge_proj_repr : Projection.Repr.t -> Projection.Repr.t
val discharge_abstract_universe_context :
  Declarations.abstr_info -> Univ.AbstractContext.t -> Univ.universe_level_subst * Univ.AbstractContext.t
