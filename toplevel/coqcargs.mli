(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type compilation_mode = BuildVo | BuildVio | Vio2Vo

type t =
  { compilation_mode : compilation_mode

  ; compile_list: (string * bool) list  (* bool is verbosity  *)
  ; compilation_output_name : string option

  ; vio_checking : bool
  ; vio_tasks    : (int list * string) list
  ; vio_files    : string list
  ; vio_files_j  : int

  ; echo : bool

  ; outputstate : string option
  }

val default : t
val parse : string list -> t
