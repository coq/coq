
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
  | Module of string
  | OpenedSection of string * Summary.frozen
  | FrozenState of Summary.frozen

and library_entry = section_path * node

and library_segment = library_entry list


(*s Adding operations (which calls the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : identifier -> path_kind -> obj -> section_path
val add_anonymous_leaf : obj -> unit

val contents_after : section_path option -> library_segment


(*s Opening and closing a section. *)

val open_section : string -> section_path
val close_section : string -> section_path * library_segment * Summary.frozen

val make_path : identifier -> path_kind -> section_path
val cwd : unit -> string list
val is_section_p : section_path -> bool

val start_module : string -> unit
val export_module : unit -> library_segment


(*s Backtracking (undo). *)

val reset_to : section_path -> unit
val reset_name : identifier -> unit


(*s We can get and set the state of the operations (used in [States]). *)

type frozen

val freeze : unit -> frozen
val unfreeze : frozen -> unit

val init : unit -> unit

val declare_initial_state : unit -> unit
val reset_initial : unit -> unit
