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

module State : sig
  type t
  val loadpath : t -> Loadpath.State.t
end

(** [init args] Init coqdep, setting arguments from [args]. *)
val init : Args.t -> State.t

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

val sort : State.t -> unit

val compute_deps : State.t -> Dep_info.t list
