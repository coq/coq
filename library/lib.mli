(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Identifier
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
  | CompUnit of dir_path
  | OpenedModule of module_ident * Summary.frozen
  | OpenedModtype of module_ident * Summary.frozen
  | OpenedSection of module_ident * Summary.frozen
  (* bool is to tell if the section must be opened automatically *)
  | ClosedSection of bool * module_ident * library_segment
  | FrozenState of Summary.frozen

and library_entry = section_path * node

and library_segment = library_entry list


val open_segment : library_segment -> unit
val load_segment : library_segment -> unit
val subst_segment : substitution -> library_segment -> library_segment



(*s Adding operations (which calls the [cache] method, and getting the
  current list of operations (most recent ones coming first). *)

val add_leaf : identifier -> path_kind -> obj -> section_path
val add_leaves : library_segment -> identifier -> path_kind -> obj -> section_path
val add_anonymous_leaf : obj -> unit
val add_frozen_state : unit -> unit


(*s The function [contents_after] returns the current library segment, 
    starting from a given section path. If not given, the entire segment
    is returned. *)

val contents_after : section_path option -> library_segment


(*s Opening and closing a section. *)

val open_section : identifier -> section_path
val close_section : 
  bool -> identifier -> section_path * library_segment * Summary.frozen
val sections_are_opened : unit -> bool

val make_path : identifier -> path_kind -> section_path
val cwd : unit -> dir_path
val is_section_p : dir_path -> bool

(*s Compilation units *)

val start_comp_unit : dir_path -> unit
val comp_unit_name : module_ident -> dir_path
val export_comp_unit : dir_path -> library_segment * library_segment

(*s Modules *)

val begin_module : module_ident -> Summary.frozen -> section_path
val end_module : 
  module_ident -> section_path * dir_path * Summary.frozen * 
    library_segment * library_segment * library_segment

val begin_modtype : module_ident -> Summary.frozen -> section_path
val end_modtype : 
  module_ident -> section_path * dir_path * Summary.frozen * 
    library_segment * library_segment

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
