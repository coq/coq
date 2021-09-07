(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Pattern
open Vernacexpr

(** {6 Search facilities. } *)

type glob_search_item =
  | GlobSearchSubPattern of glob_search_where * bool * constr_pattern
  | GlobSearchString of string
  | GlobSearchKind of Decls.logical_kind
  | GlobSearchFilter of (GlobRef.t -> bool)

type glob_search_request =
  | GlobSearchLiteral of glob_search_item
  | GlobSearchDisjConj of (bool * glob_search_request) list list

type filter_function =
  GlobRef.t -> Decls.logical_kind option -> env -> Evd.evar_map -> constr -> bool
type display_function =
  GlobRef.t -> Decls.logical_kind option -> env -> constr -> unit

(** {6 Generic filter functions} *)

val blacklist_filter : filter_function
(** Check whether a reference is blacklisted. *)

val module_filter : DirPath.t list * bool -> filter_function
(** Check whether a reference pertains or not to a set of modules *)

val search_filter : glob_search_item -> filter_function

(** {6 Specialized search functions}

[search_xxx gl pattern modinout] searches the hypothesis of the [gl]th
goal and the global environment for things matching [pattern] and
satisfying module exclude/include clauses of [modinout]. *)

val search_rewrite : env -> Evd.evar_map -> constr_pattern -> DirPath.t list * bool
                  -> display_function -> unit
val search_pattern : env -> Evd.evar_map -> constr_pattern -> DirPath.t list * bool
                  -> display_function -> unit
val search         : env -> Evd.evar_map -> (bool * glob_search_request) list
                  -> DirPath.t list * bool -> display_function -> unit

type search_constraint =
  | Name_Pattern of Str.regexp
  (** Whether the name satisfies a regexp (uses Ocaml Str syntax) *)
  | Type_Pattern of Pattern.constr_pattern
  (** Whether the object type satisfies a pattern *)
  | SubType_Pattern of Pattern.constr_pattern
  (** Whether some subtype of object type satisfies a pattern *)
  | In_Module of Names.DirPath.t
  (** Whether the object pertains to a module *)
  | Include_Blacklist
  (** Bypass the Search blacklist *)

type 'a coq_object = {
  coq_object_prefix : string list;
  coq_object_qualid : string list;
  coq_object_object : 'a;
}

val interface_search : env -> Evd.evar_map -> (search_constraint * bool) list -> constr coq_object list

(** {6 Generic search function} *)

val generic_search : env -> display_function -> unit
(** This function iterates over all hypothesis of the goal numbered
    [glnum] (if present) and all known declarations. *)

(** {6 Search function modifiers} *)

val prioritize_search : (display_function -> unit) -> display_function -> unit
(** [prioritize_search iter] iterates over the values of [iter] (seen
    as a sequence of declarations), in a relevance order. This requires to
    perform the entire iteration of [iter] before starting streaming. So
    [prioritize_search] should not be used for low-latency streaming. *)
