(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


(** Lib: record of operations, backtrack, low-level sections *)

(** This module provides a general mechanism to keep a trace of all operations
   and to backtrack (undo) those operations. It provides also the section
   mechanism (at a low level; discharge is not known at this step). *)

type is_type = bool (* Module Type or just Module *)
type export = bool option (* None for a Module Type *)

type node =
  | Leaf of Libobject.obj
  | CompilingLibrary of Libnames.object_prefix
  | OpenedModule of is_type * export * Libnames.object_prefix * Summary.frozen
  | ClosedModule  of library_segment
  | OpenedSection of Libnames.object_prefix * Summary.frozen
  | ClosedSection of library_segment
  | FrozenState of Summary.frozen

and library_segment = (Libnames.object_name * node) list

type lib_objects = (Names.Id.t * Libobject.obj) list

(** {6 Object iteration functions. } *)

val open_objects : int -> Libnames.object_prefix -> lib_objects -> unit
val load_objects : int -> Libnames.object_prefix -> lib_objects -> unit
val subst_objects : Mod_subst.substitution -> lib_objects -> lib_objects
(*val load_and_subst_objects : int -> Libnames.object_prefix -> Mod_subst.substitution -> lib_objects -> lib_objects*)

(** [classify_segment seg] verifies that there are no OpenedThings,
   clears ClosedSections and FrozenStates and divides Leafs according
   to their answers to the [classify_object] function in three groups:
   [Substitute], [Keep], [Anticipate] respectively.  The order of each
   returned list is the same as in the input list. *)
val classify_segment :
  library_segment -> lib_objects * lib_objects * Libobject.obj list

(** [segment_of_objects prefix objs] forms a list of Leafs *)
val segment_of_objects :
  Libnames.object_prefix -> lib_objects -> library_segment


(** {6 ... } *)
(** Adding operations (which call the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : Names.Id.t -> Libobject.obj -> Libnames.object_name
val add_anonymous_leaf : Libobject.obj -> unit

(** this operation adds all objects with the same name and calls [load_object]
   for each of them *)
val add_leaves : Names.Id.t -> Libobject.obj list -> Libnames.object_name

val add_frozen_state : unit -> unit

(** {6 ... } *)

(** The function [contents] gives access to the current entire segment *)

val contents : unit -> library_segment

(** The function [contents_after] returns the current library segment,
  starting from a given section path. *)

val contents_after : Libnames.object_name -> library_segment

(** {6 Functions relative to current path } *)

(** User-side names *)
val cwd : unit -> Names.DirPath.t
val cwd_except_section : unit -> Names.DirPath.t
val current_dirpath : bool -> Names.DirPath.t (* false = except sections *)
val make_path : Names.Id.t -> Libnames.full_path
val make_path_except_section : Names.Id.t -> Libnames.full_path

(** Kernel-side names *)
val current_mp : unit -> Names.module_path
val make_kn : Names.Id.t -> Names.kernel_name

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
val current_mod_id : unit -> Names.module_ident

(** Returns the opening node of a given name *)
val find_opening_node : Names.Id.t -> node

(** {6 Modules and module types } *)

val start_module :
  export -> Names.module_ident -> Names.module_path ->
  Summary.frozen -> Libnames.object_prefix

val start_modtype :
  Names.module_ident -> Names.module_path ->
  Summary.frozen -> Libnames.object_prefix

val end_module :
  unit ->
  Libnames.object_name * Libnames.object_prefix *
    Summary.frozen * library_segment

val end_modtype :
  unit ->
  Libnames.object_name * Libnames.object_prefix *
    Summary.frozen * library_segment

(** [Lib.add_frozen_state] must be called after each of the above functions *)

(** {6 Compilation units } *)

val start_compilation : Names.DirPath.t -> Names.module_path -> unit
val end_compilation_checks : Names.DirPath.t -> Libnames.object_name
val end_compilation :
  Libnames.object_name-> Libnames.object_prefix * library_segment

(** The function [library_dp] returns the [DirPath.t] of the current
   compiling library (or [default_library]) *)
val library_dp : unit -> Names.DirPath.t

(** Extract the library part of a name even if in a section *)
val dp_of_mp : Names.module_path -> Names.DirPath.t
val split_mp : Names.module_path -> Names.DirPath.t * Names.DirPath.t
val split_modpath : Names.module_path -> Names.DirPath.t * Names.Id.t list
val library_part :  Globnames.global_reference -> Names.DirPath.t
val remove_section_part : Globnames.global_reference -> Names.DirPath.t

(** {6 Sections } *)

val open_section : Names.Id.t -> unit
val close_section : unit -> unit

(** {6 We can get and set the state of the operations (used in [States]). } *)

type frozen

val freeze : marshallable:Summary.marshallable -> frozen
val unfreeze : frozen -> unit

val init : unit -> unit

(** {6 Section management for discharge } *)
type variable_info = Names.Id.t * Decl_kinds.binding_kind *
    Term.constr option * Term.types
type variable_context = variable_info list 
type abstr_info = variable_context * Univ.universe_level_subst * Univ.UContext.t

val instance_from_variable_context : variable_context -> Names.Id.t array
val named_of_variable_context : variable_context -> Context.named_context

val section_segment_of_constant : Names.constant -> abstr_info
val section_segment_of_mutual_inductive: Names.mutual_inductive -> abstr_info

val section_instance : Globnames.global_reference -> Univ.universe_instance * Names.Id.t array
val is_in_section : Globnames.global_reference -> bool

val add_section_variable : Names.Id.t -> Decl_kinds.binding_kind -> Decl_kinds.polymorphic -> Univ.universe_context_set -> unit

val add_section_constant : bool (* is_projection *) -> 
  Names.constant -> Context.named_context -> unit
val add_section_kn : Names.mutual_inductive -> Context.named_context -> unit
val replacement_context : unit -> Opaqueproof.work_list

(** {6 Discharge: decrease the section level if in the current section } *)

val discharge_kn :  Names.mutual_inductive -> Names.mutual_inductive
val discharge_con : Names.constant -> Names.constant
val discharge_global : Globnames.global_reference -> Globnames.global_reference
val discharge_inductive : Names.inductive -> Names.inductive

(* discharging a constant in one go *)
val full_replacement_context : unit -> Opaqueproof.work_list list
val full_section_segment_of_constant :
  Names.constant -> (Context.named_context -> Context.named_context) list


