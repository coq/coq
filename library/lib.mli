(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Libnames
open Libobject
open Summary
(*i*)

(*s This module provides a general mechanism to keep a trace of all operations
   and to backtrack (undo) those operations. It provides also the section
   mechanism (at a low level; discharge is not known at this step). *)

type node = 
  | Leaf of obj
  | Module of dir_path
  | OpenedSection of (dir_path * dir_path) * Summary.frozen
  | ClosedSection of bool * dir_path * library_segment
  | FrozenState of Summary.frozen

and library_entry = section_path * node

and library_segment = library_entry list


(*s Adding operations (which calls the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : identifier -> obj -> section_path
val add_absolutely_named_leaf : section_path -> obj -> unit
val add_anonymous_leaf : obj -> unit
val add_frozen_state : unit -> unit
val mark_end_of_command : unit -> unit

(*s The function [contents_after] returns the current library segment, 
  starting from a given section path. If not given, the entire segment
  is returned. *)

val contents_after : section_path option -> library_segment


(*s Opening and closing a section. *)

(* the second [dir_path] returned by [open_section] is the path relative
   to the curent module *)
val open_section : identifier -> section_path * dir_path

(* the second [dir_path] returned by [close_section] is relative, as above *)
val close_section : export:bool -> identifier -> 
  dir_path * dir_path * library_segment * Summary.frozen

val sections_are_opened : unit -> bool

val make_path : identifier -> section_path
val make_kn : identifier -> kernel_name

val cwd : unit -> dir_path
val sections_depth : unit -> int
val is_section_p : dir_path -> bool

val start_module : dir_path -> unit
val end_module : module_ident -> dir_path
val export_module : dir_path -> library_segment

val module_dp : unit -> dir_path

(*s Backtracking (undo). *)

val reset_to : section_path -> unit
val reset_name : identifier -> unit
val back : int -> unit

(*s We can get and set the state of the operations (used in [States]). *)

type frozen

val freeze : unit -> frozen
val unfreeze : frozen -> unit

val init : unit -> unit

val declare_initial_state : unit -> unit
val reset_initial : unit -> unit
