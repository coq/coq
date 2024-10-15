(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compilation modes:
  - BuildVo      : process statements and proofs (standard compilation),
                   and also output an empty .vos file and .vok file
  - BuildVos     : process statements, and discard proofs,
                   and load .vos files for required libraries
  - BuildVok     : like BuildVo, but load .vos files for required libraries

  When loading the .vos version of a required library, if the file exists but is
  empty, then we attempt to load the .vo version of that library.
  This trick is useful to avoid the need for the user to compile .vos version
  when an up to date .vo version is already available.
*)
type compilation_mode = BuildVo | BuildVos | BuildVok

type t =
  { compilation_mode : compilation_mode

  ; compile_file: (string * bool) option  (* bool is verbosity  *)
  ; compilation_output_name : string option

  ; echo : bool

  ; glob_out    : Dumpglob.glob_output

  ; output_context : bool
  }

val default : t
val parse : string list -> t
