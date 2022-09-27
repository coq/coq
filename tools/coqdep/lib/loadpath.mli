(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** To move  *)
val get_extension : string -> string list -> string * string

(* Loadpaths *)
type basename = string
type dirname = System.unix_path
type dir = string option
type filename = string
type dirpath = string list
type root = filename * dirpath

type result =
  | ExactMatches of filename list
  | PartialMatchesInSameRoot of root * filename list

module State : sig
  type t

  val make : boot:bool -> t
end

val search_v_known : State.t -> ?from:dirpath -> dirpath -> result option
val search_other_known : State.t -> ?from:dirpath -> dirpath -> result option
val search_mllib_known : State.t -> string -> dir option
val search_mlpack_known : State.t -> string -> dir option

val add_caml_dir : State.t -> dirname -> unit

(** Simply add this directory and imports it, no subdirs. This is used
    by the implicit adding of the current path. *)
val add_current_dir : State.t -> dirname -> unit

(** [add_loadpath st ~implicit ~in_tree dn dp] Adds a loadpath to
   coqdep's search path. [implicit] controls -Q/-R options, [in_tree]
   controls whether the path was added by the user or by Coq's auto
   initialization. *)
val add_loadpath : State.t -> implicit:bool -> in_tree:bool -> dirname -> dirpath -> unit

(** [find_dir_logpath phys_dir] Return the logical path of directory
   [dir] if it has been given one. Raise [Not_found] otherwise. In
   particular we can check if "." has been attributed a logical path
   after processing all options and silently give the default one if
   it hasn't. We may also use this to warn if ap hysical path is met
   twice.*)
val find_dir_logpath : string -> string list

(* Used only in "canonize" *)
val absolute_dir : string -> string
val absolute_file_name : filename_concat:(string -> string -> string) -> string -> string option -> string
