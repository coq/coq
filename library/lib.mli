
(* $Id$ *)

(*i*)
open Names
open Libobject
open Summary
(*i*)

(* This module provides a general mechanism to keep a trace of all operations
   and to backtrack (undo) those operations. It provides also the section
   mechanism (at a low level; discharge is not known at this step). *)

type node = 
  | Leaf of obj
  | OpenedSection of string * module_p
  | ClosedSection of string * module_p * library_segment
  | FrozenState of Summary.frozen

and library_segment = (section_path * node) list

and module_p = bool

type library_entry = section_path * node


(*s Adding operations, and getting the current list of operations (most 
  recent ones coming first). *)

val add_leaf : identifier -> path_kind -> obj -> section_path
val add_anonymous_leaf : obj -> unit

val contents_after : section_path option -> library_segment


(*s Opening and closing a section. The boolean in [open_section] indicates
  a module. *)

val open_section : string -> bool -> section_path
val close_section : string -> unit

val make_path : identifier -> path_kind -> section_path
val cwd : unit -> string list


(*s Backtracking (undo). *)

val reset_to : section_path -> unit


(*s We can get and set the state of the operations (used in [States]). *)

type frozen

val freeze : unit -> frozen
val unfreeze : frozen -> unit

val init : unit -> unit
