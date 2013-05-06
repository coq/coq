(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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
(** The function [contents_after] returns the current library segment,
  starting from a given section path. If not given, the entire segment
  is returned. *)

val contents_after : Libnames.object_name option -> library_segment

(** {6 Functions relative to current path } *)

(** User-side names *)
val cwd : unit -> Names.DirPath.t
val cwd_except_section : unit -> Names.DirPath.t
val current_dirpath : bool -> Names.DirPath.t (* false = except sections *)
val make_path : Names.Id.t -> Libnames.full_path
val make_path_except_section : Names.Id.t -> Libnames.full_path
val path_of_include : unit -> Libnames.full_path

(** Kernel-side names *)
val current_prefix : unit -> Names.module_path * Names.DirPath.t
val make_kn : Names.Id.t -> Names.kernel_name
val make_con : Names.Id.t -> Names.constant

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
val end_compilation : Names.DirPath.t -> Libnames.object_prefix * library_segment

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

(** {6 Backtracking } *)

(** NB: The next commands are low-level ones, do not use them directly
    otherwise the command history stack in [Backtrack] will be out-of-sync.
    Also note that [reset_initial] is now [reset_label first_command_label] *)

(** Adds a "dummy" entry in lib_stk with a unique new label number. *)
val mark_end_of_command : unit -> unit

(** Returns the current label number *)
val current_command_label : unit -> int

(** [reset_label n] resets [lib_stk] to the label n registered by
   [mark_end_of_command()]. It forgets anything registered after
   this label. The label should be strictly in the past. *)
val reset_label : int -> unit

(** [raw_reset_initial] is now [reset_label] to the first label.
    This is meant to be used during initial Load's and compilations.
    Otherwise, consider instead [Backtrack.reset_initial] *)
val raw_reset_initial : unit -> unit

(** search the label registered immediately before adding some definition *)
val label_before_name : Names.Id.t Loc.located -> int

(** {6 We can get and set the state of the operations (used in [States]). } *)

type frozen

val freeze : marshallable:bool -> frozen
val unfreeze : frozen -> unit

val init : unit -> unit

(** XML output hooks *)
val set_xml_open_section : (Names.Id.t -> unit) -> unit
val set_xml_close_section : (Names.Id.t -> unit) -> unit

(** {6 Section management for discharge } *)
type variable_info = Names.Id.t * Decl_kinds.binding_kind *
    Term.constr option * Term.types
type variable_context = variable_info list

val instance_from_variable_context : variable_context -> Names.Id.t array
val named_of_variable_context : variable_context -> Context.named_context

val section_segment_of_constant : Names.constant -> variable_context
val section_segment_of_mutual_inductive: Names.mutual_inductive -> variable_context

val section_instance : Globnames.global_reference -> Names.Id.t array
val is_in_section : Globnames.global_reference -> bool

val add_section_variable : Names.Id.t -> Decl_kinds.binding_kind -> unit

val add_section_constant : Names.constant -> Context.named_context -> unit
val add_section_kn : Names.mutual_inductive -> Context.named_context -> unit
val replacement_context : unit ->
  (Names.Id.t array Names.Cmap.t * Names.Id.t array Names.Mindmap.t)

(** {6 Discharge: decrease the section level if in the current section } *)

val discharge_kn :  Names.mutual_inductive -> Names.mutual_inductive
val discharge_con : Names.constant -> Names.constant
val discharge_global : Globnames.global_reference -> Globnames.global_reference
val discharge_inductive : Names.inductive -> Names.inductive


