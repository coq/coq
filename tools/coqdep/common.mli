(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module StrSet : Set.S with type elt = string

val coqdep_warning : ('a, Format.formatter, unit, unit) format4 -> 'a

type dirname = string
type basename = string
type filename = string
type dirpath = string list
type root = filename * dirpath

(** [find_dir_logpath dir] Return the logical path of directory [dir]
    if it has been given one. Raise [Not_found] otherwise. In
    particular we can check if "." has been attributed a logical path
    after processing all options and silently give the default one if
    it hasn't. We may also use this to warn if ap hysical path is met
    twice.*)
val find_dir_logpath: dirname -> dirpath

(** Options *)
val option_sort : bool ref
val option_boot : bool ref

(** ML-related manipulation *)
val add_known : bool -> root -> dirname -> dirpath -> basename -> unit
val add_coqlib_known : bool -> root -> dirname -> dirpath -> basename -> unit

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

val sort : unit -> unit

(** [init args] Init coqdep, parsing arguments from [args]; returns
   the list of .v files passed as arguments *)
val init : string list -> string list

(** Display the --help documentation *)
val usage : unit -> unit

(** [treat_file_command_line file] Add an input file to be considered  *)
val treat_file_command_line : string -> unit

module Dep : sig
  type t =
  | Require of string (* one basename, to which we later append .vo or .vio or .vos *)
  | Other of string   (* filenames of dependencies, separated by spaces *)
end

module Dep_info : sig
  type t =
    { name : string
    ; deps : Dep.t list
    }

  (** Print dependencies in makefile format *)
  val print : Format.formatter -> t -> unit
end

val compute_deps : unit -> Dep_info.t list
