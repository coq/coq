(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val getenv_opt : string -> string option

val getenv_rocq : string -> string option
(** [getenv_rocq name] returns the value of "ROCQ$name" if it exists,
    otherwise the value of "COQ$name" if it exists and warns that it
    is deprecated, otherwise [None]. *)

val getenv_rocq_gen : rocq:string -> coq:string -> string option
(** [getenv_rocq_gen ~rocq ~coq] returns the value of [rocq] if it
    exists, otherwise the value of [coq] if it exists and warns that
    it is deprecated, otherwise [None]. *)

val set_warn_deprecated_coq_var : (rocq:string -> coq:string -> unit) -> unit

val canonical_path_name : string -> string
(** If the path does not exist, returns it prefixed with cwd. *)

val use_suffix : string -> string -> string
(** [use_suffix prefix suffix] adds a local installation suffix (unless
    the suffix is itself absolute in which case the prefix does not
    matter) *)
