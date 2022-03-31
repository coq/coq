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

(** Options *)
val option_sort : bool ref

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

  val to_string : suffix:string -> t -> string
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
