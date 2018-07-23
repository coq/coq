(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.
Require Import Std.

Ltac2 @ external get : ident list -> Std.reference option := "ltac2" "env_get".
(** Returns the global reference corresponding to the absolute name given as
    argument if it exists. *)

Ltac2 @ external expand : ident list -> Std.reference list := "ltac2" "env_expand".
(** Returns the list of all global references whose absolute name contains
    the argument list as a prefix. *)

Ltac2 @ external path : Std.reference -> ident list := "ltac2" "env_path".
(** Returns the absolute name of the given reference. Panics if the reference
    does not exist. *)
