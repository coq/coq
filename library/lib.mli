(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Libnames
open Libobject
open Summary
open Mod_subst
(*i*)

(*s This module provides a general mechanism to keep a trace of all operations
   and to backtrack (undo) those operations. It provides also the section
   mechanism (at a low level; discharge is not known at this step). *)

type node = 
  | Leaf of obj
  | CompilingLibrary of object_prefix
  | OpenedModule of bool option * object_prefix * Summary.frozen
  | ClosedModule  of library_segment
  | OpenedModtype of object_prefix * Summary.frozen
  | ClosedModtype of library_segment
  | OpenedSection of object_prefix * Summary.frozen
  | ClosedSection of library_segment
  | FrozenState of Summary.frozen

and library_segment = (object_name * node) list

type lib_objects = (identifier * obj) list

(*s Object iteratation functions. *)

val open_objects : int -> object_prefix -> lib_objects -> unit
val load_objects : int -> object_prefix -> lib_objects -> unit
val subst_objects : object_prefix -> substitution -> lib_objects -> lib_objects

(* [classify_segment seg] verifies that there are no OpenedThings,
   clears ClosedSections and FrozenStates and divides Leafs according
   to their answers to the [classify_object] function in three groups:
   [Substitute], [Keep], [Anticipate] respectively.  The order of each
   returned list is the same as in the input list. *)
val classify_segment : 
  library_segment -> lib_objects * lib_objects * obj list

(* [segment_of_objects prefix objs] forms a list of Leafs *)
val segment_of_objects :
  object_prefix -> lib_objects -> library_segment


(*s Adding operations (which call the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : identifier -> obj -> object_name
val add_absolutely_named_leaf : object_name -> obj -> unit
val add_anonymous_leaf : obj -> unit

(* this operation adds all objects with the same name and calls [load_object]
   for each of them *)
val add_leaves : identifier -> obj list -> object_name

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

val contents_after : object_name option -> library_segment

(*s Functions relative to current path *)

(* User-side names *)
val cwd : unit -> dir_path
val make_path : identifier -> section_path
val path_of_include : unit -> section_path

(* Kernel-side names *)
val current_prefix : unit -> module_path * dir_path
val make_kn : identifier -> kernel_name
val make_con : identifier -> constant

(* Are we inside an opened section *)
val sections_are_opened : unit -> bool
val sections_depth : unit -> int

(* Are we inside an opened module type *)
val is_modtype : unit -> bool
val is_module : unit -> bool
val current_mod_id : unit -> module_ident

(* Returns the most recent OpenedThing node *)
val what_is_opened : unit -> object_name * node


(*s Modules and module types *)

val start_module : 
  bool option -> module_ident -> module_path -> Summary.frozen -> object_prefix
val end_module : module_ident 
  -> object_name * object_prefix * Summary.frozen * library_segment

val start_modtype : 
  module_ident -> module_path -> Summary.frozen -> object_prefix
val end_modtype : module_ident 
  -> object_name * object_prefix * Summary.frozen * library_segment
(* [Lib.add_frozen_state] must be called after each of the above functions *)

(*s Compilation units *)

val start_compilation : dir_path -> module_path -> unit
val end_compilation : dir_path -> object_prefix * library_segment

(* The function [library_dp] returns the [dir_path] of the current
   compiling library (or [default_library]) *)
val library_dp : unit -> dir_path

(* Extract the library part of a name even if in a section *)
val library_part :  global_reference -> dir_path
val remove_section_part : global_reference -> dir_path

(*s Sections *)

val open_section : identifier -> unit
val close_section : identifier -> unit

(*s Backtracking (undo). *)

val reset_to : object_name -> unit
val reset_name : identifier located -> unit
val remove_name : identifier located -> unit
val reset_mod : identifier located -> unit

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
val set_xml_open_section : (identifier -> unit) -> unit
val set_xml_close_section : (identifier -> unit) -> unit


(*s Section management for discharge *)

val section_segment_of_constant : constant -> Sign.named_context
val section_segment_of_mutual_inductive: mutual_inductive -> Sign.named_context

val section_instance : global_reference -> identifier array

val add_section_variable : identifier -> bool -> Term.types option -> unit
val add_section_constant : constant -> Sign.named_context -> unit
val add_section_kn : kernel_name -> Sign.named_context -> unit
val replacement_context : unit ->
  (identifier array Cmap.t * identifier array KNmap.t)

(*s Discharge: decrease the section level if in the current section *)

val discharge_kn :  kernel_name -> kernel_name
val discharge_con : constant -> constant
val discharge_global : global_reference -> global_reference
val discharge_inductive : inductive -> inductive


