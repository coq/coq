(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Term
open Environ
open Pattern
open Globnames
open Nametab

(** {6 Search facilities. } *)

type glob_search_about_item =
  | GlobSearchSubPattern of constr_pattern
  | GlobSearchString of string

type filter_function = global_reference -> env -> constr -> bool
type display_function = global_reference -> env -> constr -> unit

(** {6 Generic filter functions} *)

val blacklist_filter : filter_function
(** Check whether a reference is blacklisted. *)

val module_filter : DirPath.t list * bool -> filter_function
(** Check whether a reference pertains or not to a set of modules *)

val search_about_filter : glob_search_about_item -> filter_function
(** Check whether a reference matches a SearchAbout query. *)

(** {6 Specialized search functions} *)

val search_by_head : constr_pattern -> DirPath.t list * bool -> std_ppcmds
val search_rewrite : constr_pattern -> DirPath.t list * bool -> std_ppcmds
val search_pattern : constr_pattern -> DirPath.t list * bool -> std_ppcmds
val search_about   : (bool * glob_search_about_item) list ->
  DirPath.t list * bool -> std_ppcmds
val interface_search : (Interface.search_constraint * bool) list ->
  string Interface.coq_object list

(** {6 Generic search function} *)

val generic_search : display_function -> unit
(** This function iterates over all known declarations *)
