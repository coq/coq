(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.String.

Ltac2 @external file_write : string -> string -> unit := "ltac2" "system_file_write".
Ltac2 @external file_append : string -> string -> unit := "ltac2" "system_file_append".

(** Write a Coq String to a named file *)

Ltac2 file_write_coq_string (file : string) (str : constr) :=
  file_write file (String.of_coq_string str).

(** Append a Coq String to a named file *)

Ltac2 file_append_coq_string (file : string) (str : constr) :=
  file_append file (String.of_coq_string str).
