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

val search_by_head : constr -> Dir_path.t list * bool -> std_ppcmds
val search_rewrite : constr -> Dir_path.t list * bool -> std_ppcmds
val search_pattern : constr -> Dir_path.t list * bool -> std_ppcmds
val search_about  :
  (bool * glob_search_about_item) list -> Dir_path.t list * bool -> std_ppcmds

val interface_search : (Interface.search_constraint * bool) list ->
  string Interface.coq_object list

(** The filtering function that is by standard search facilities.
   It can be passed as argument to the raw search functions. *)

val filter_by_module_from_list : Dir_path.t list * bool -> filter_function

val filter_blacklist : filter_function

(** raw search functions can be used for various extensions. *)
val gen_filtered_search : filter_function -> display_function -> unit
val filtered_search : filter_function -> display_function -> global_reference -> unit
val raw_pattern_search : filter_function -> display_function -> constr_pattern -> unit
val raw_search_rewrite : filter_function -> display_function -> constr_pattern -> unit
val raw_search_about : filter_function -> display_function -> (bool * glob_search_about_item) list -> unit
val raw_search_by_head : filter_function -> display_function -> constr_pattern -> unit
