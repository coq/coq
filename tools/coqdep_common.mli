(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

val option_c : bool ref
val option_noglob : bool ref
val option_boot : bool ref

type dynlink = Opt | Byte | Both | No | Variable

val option_dynlink : dynlink ref
val option_mldep : string option ref
val norec_dirs : StrSet.t ref
val suffixe : string ref
type dir = string option
val get_extension : string -> string list -> string * string
val basename_noext : string -> string
val mlAccu : (string * string * dir) list ref
val mliAccu : (string * dir) list ref
val mllibAccu : (string * dir) list ref
val vAccu : (string * string) list ref
val addQueue : 'a list ref -> 'a -> unit
val add_ml_known : string -> dir -> string -> unit
val iter_ml_known : (string -> dir -> unit) -> unit
val search_ml_known : string -> dir option
val add_mli_known : string -> dir -> string -> unit
val iter_mli_known : (string -> dir -> unit) -> unit
val search_mli_known : string -> dir option
val add_mllib_known : string -> dir -> string -> unit
val search_mllib_known : string -> dir option
val search_v_known : ?from:string list -> string list -> string option
val file_name : string -> string option -> string
val escape : string -> string
val canonize : string -> string
val mL_dependencies : unit -> unit
val coq_dependencies : unit -> unit
val suffixes : 'a list -> 'a list list
val add_known : bool -> string -> string list -> string -> unit
val add_coqlib_known : bool -> string -> string list -> string -> unit
val add_caml_known : string -> string list -> string -> unit
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

val treat_file : dir -> string -> unit
val error_cannot_parse : string -> int * int -> 'a
