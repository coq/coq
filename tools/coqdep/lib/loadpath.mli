(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
type dirname = string
type dir = string option
type filename = string
type dirpath = string list
type root = filename * dirpath

type result =
  | ExactMatches of filename list
  | PartialMatchesInSameRoot of root * filename list

module State : sig
  type t

  val make : worker:string option -> boot:bool -> t
end

val get_worker_path : State.t -> string

val search_v_known : State.t -> ?from:dirpath -> dirpath -> result option
val search_other_known : State.t -> ?from:dirpath -> dirpath -> result option

val is_in_coqlib : State.t -> ?from:dirpath -> dirpath -> bool

val add_current_dir : State.t -> System.unix_path -> unit
val add_q_include : State.t -> System.unix_path -> string -> unit
val add_r_include : State.t -> System.unix_path -> string -> unit

(* These should disappear in favor of add_q / add_r *)

(** Simply add this directory and imports it, no subdirs. This is used
    by the implicit adding of the current path. *)
val add_norec_dir_import :
  (bool -> root -> dirname -> dirpath -> basename -> unit) -> dirname -> dirpath -> unit

(** -Q semantic: go in subdirs but only full logical paths are known. *)
val add_rec_dir_no_import :
  (bool -> root -> dirname -> dirpath -> basename -> unit) -> dirname -> dirpath -> unit

(** -R semantic: go in subdirs and suffixes of logical paths are known. *)
val add_rec_dir_import :
  (bool -> root -> dirname -> dirpath -> basename -> unit) -> dirname -> dirpath -> unit

val add_known : State.t -> bool -> root -> dirname -> dirpath -> basename -> unit
val add_coqlib_known : State.t -> bool -> root -> dirname -> dirpath -> basename -> unit

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
