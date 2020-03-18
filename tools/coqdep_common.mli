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

(** [find_dir_logpath dir] Return the logical path of directory [dir]
    if it has been given one. Raise [Not_found] otherwise. In
    particular we can check if "." has been attributed a logical path
    after processing all options and silently give the default one if
    it hasn't. We may also use this to warn if ap hysical path is met
    twice.*)
val find_dir_logpath: string -> string list

(** Options *)
val option_noglob : bool ref
val option_boot : bool ref
val write_vos : bool ref

type dynlink = Opt | Byte | Both | No | Variable
val option_dynlink : dynlink ref

val norec_dirs : StrSet.t ref

type dir = string option
val treat_file : dir -> string -> unit

(** ML-related manipulation *)
val coq_dependencies : unit -> unit
val add_known : bool -> string -> string list -> string -> unit
val add_coqlib_known : bool -> string -> string list -> string -> unit

(* Used to locate plugins for [Declare ML Module] *)
val add_caml_dir : string -> unit

(** Simply add this directory and imports it, no subdirs. This is used
    by the implicit adding of the current path. *)
val add_norec_dir_import :
  (bool -> string -> string list -> string -> unit) -> string -> string list -> unit

(** -Q semantic: go in subdirs but only full logical paths are known. *)
val add_rec_dir_no_import :
  (bool -> string -> string list -> string -> unit) -> string -> string list -> unit

(** -R semantic: go in subdirs and suffixes of logical paths are known. *)
val add_rec_dir_import :
  (bool -> string -> string list -> string -> unit) -> string -> string list -> unit

val sort : unit -> unit
