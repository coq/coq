(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module StrSet : Set.S with type elt = string

module State : sig
  type t
  val loadpath : t -> Loadpath.State.t
end

(** [init args] Init coqdep, setting arguments from [args]. *)
val init : make_separator_hack:bool -> Args.t -> State.t

(** [treat_file_command_line file] Add an input file to be considered  *)
val treat_file_command_line : string -> unit

val sort : State.t -> unit

val compute_deps : State.t -> Dep_info.t list
