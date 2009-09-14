(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)


(*s This module provides a general mechanism to keep a trace of all operations
   and to backtrack (undo) those operations. It provides also the section
   mechanism (at a low level; discharge is not known at this step). *)

type node = 
  | Leaf of Libobject.obj
  | CompilingLibrary of Libnames.object_prefix
  | OpenedModule of bool option * Libnames.object_prefix * Summary.frozen
  | ClosedModule  of library_segment
  | OpenedModtype of Libnames.object_prefix * Summary.frozen
  | ClosedModtype of library_segment
  | OpenedSection of Libnames.object_prefix * Summary.frozen
  | ClosedSection of library_segment
  | FrozenState of Summary.frozen

and library_segment = (Libnames.object_name * node) list

type lib_objects = (Names.identifier * Libobject.obj) list

(*s Object iteratation functions. *)

val open_objects : int -> Libnames.object_prefix -> lib_objects -> unit
val load_objects : int -> Libnames.object_prefix -> lib_objects -> unit
val subst_objects : Libnames.object_prefix -> Mod_subst.substitution -> lib_objects -> lib_objects
val load_and_subst_objects : int -> Libnames.object_prefix -> Mod_subst.substitution -> lib_objects -> lib_objects

(* [classify_segment seg] verifies that there are no OpenedThings,
   clears ClosedSections and FrozenStates and divides Leafs according
   to their answers to the [classify_object] function in three groups:
   [Substitute], [Keep], [Anticipate] respectively.  The order of each
   returned list is the same as in the input list. *)
val classify_segment : 
  library_segment -> lib_objects * lib_objects * Libobject.obj list

(* [segment_of_objects prefix objs] forms a list of Leafs *)
val segment_of_objects :
  Libnames.object_prefix -> lib_objects -> library_segment


(*s Adding operations (which call the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : Names.identifier -> Libobject.obj -> Libnames.object_name
val add_anonymous_leaf : Libobject.obj -> unit

(* this operation adds all objects with the same name and calls [load_object]
   for each of them *)
val add_leaves : Names.identifier -> Libobject.obj list -> Libnames.object_name

val add_frozen_state : unit -> unit

(* Adds a "dummy" entry in lib_stk with a unique new label number. *)
val mark_end_of_command : unit -> unit
(* Returns the current label number *)
val current_command_label : unit -> int
(* [reset_label n ] resets [lib_stk] to the label n registered by
   [mark_end_of_command()]. That is it forgets the label and anything
   registered after it. *)
val reset_label : int -> unit

(*s The function [contents_after] returns the current library segment, 
  starting from a given section path. If not given, the entire segment
  is returned. *)

val contents_after : Libnames.object_name option -> library_segment

(*s Functions relative to current path *)

(* User-side names *)
val cwd : unit -> Names.dir_path
val current_dirpath : bool -> Names.dir_path
val make_path : Names.identifier -> Libnames.full_path
val path_of_include : unit -> Libnames.full_path

(* Kernel-side names *)
val current_prefix : unit -> Names.module_path * Names.dir_path
val make_kn : Names.identifier -> Names.kernel_name
val make_con : Names.identifier -> Names.constant

(* Are we inside an opened section *)
val sections_are_opened : unit -> bool
val sections_depth : unit -> int

(* Are we inside an opened module type *)
val is_modtype : unit -> bool
val is_module : unit -> bool
val current_mod_id : unit -> Names.module_ident

(* Returns the opening node of a given name *)
val find_opening_node : Names.identifier -> node

(*s Modules and module types *)

val start_module : 
  bool option -> Names.module_ident -> Names.module_path -> Summary.frozen -> Libnames.object_prefix
val end_module : unit
  -> Libnames.object_name * Libnames.object_prefix * Summary.frozen * library_segment

val start_modtype : 
  Names.module_ident -> Names.module_path -> Summary.frozen -> Libnames.object_prefix
val end_modtype : unit
  -> Libnames.object_name * Libnames.object_prefix * Summary.frozen * library_segment
(* [Lib.add_frozen_state] must be called after each of the above functions *)

(*s Compilation units *)

val start_compilation : Names.dir_path -> Names.module_path -> unit
val end_compilation : Names.dir_path -> Libnames.object_prefix * library_segment

(* The function [library_dp] returns the [dir_path] of the current
   compiling library (or [default_library]) *)
val library_dp : unit -> Names.dir_path

(* Extract the library part of a name even if in a section *)
val dp_of_mp : Names.module_path -> Names.dir_path
val split_mp : Names.module_path -> Names.dir_path * Names.dir_path
val split_modpath : Names.module_path -> Names.dir_path * Names.identifier list
val library_part :  Libnames.global_reference -> Names.dir_path
val remove_section_part : Libnames.global_reference -> Names.dir_path

(*s Sections *)

val open_section : Names.identifier -> unit
val close_section : unit -> unit

(*s Backtracking (undo). *)

val reset_to : Libnames.object_name -> unit
val reset_name : Names.identifier Util.located -> unit
val remove_name : Names.identifier Util.located -> unit
val reset_mod : Names.identifier Util.located -> unit
val reset_to_state : Libnames.object_name -> unit

val has_top_frozen_state : unit -> Libnames.object_name option

(* [back n] resets to the place corresponding to the $n$-th call of 
   [mark_end_of_command] (counting backwards) *)
val back : int -> unit

(*s We can get and set the state of the operations (used in [States]). *)

type frozen

val freeze : unit -> frozen
val unfreeze : frozen -> unit

val init : unit -> unit

val declare_initial_state : unit -> unit
val reset_initial : unit -> unit


(* XML output hooks *)
val set_xml_open_section : (Names.identifier -> unit) -> unit
val set_xml_close_section : (Names.identifier -> unit) -> unit

type binding_kind = Explicit | Implicit

(*s Section management for discharge *)
type variable_info = Names.identifier * binding_kind * Term.constr option * Term.types
type variable_context = variable_info list

val instance_from_variable_context : variable_context -> Names.identifier array
val named_of_variable_context : variable_context -> Sign.named_context

val section_segment_of_constant : Names.constant -> variable_context
val section_segment_of_mutual_inductive: Names.mutual_inductive -> variable_context

val section_instance : Libnames.global_reference -> Names.identifier array
val is_in_section : Libnames.global_reference -> bool

val add_section_variable : Names.identifier -> binding_kind -> unit

val add_section_constant : Names.constant -> Sign.named_context -> unit
val add_section_kn : Names.kernel_name -> Sign.named_context -> unit
val replacement_context : unit ->
  (Names.identifier array Names.Cmap.t * Names.identifier array Names.KNmap.t)

(*s Discharge: decrease the section level if in the current section *)

val discharge_kn :  Names.kernel_name -> Names.kernel_name
val discharge_con : Names.constant -> Names.constant
val discharge_global : Libnames.global_reference -> Libnames.global_reference
val discharge_inductive : Names.inductive -> Names.inductive


