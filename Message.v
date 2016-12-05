(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Coq.ltac2.Init.

Ltac2 @ external print : message -> unit := "ltac2" "print".

Ltac2 @ external of_string : string -> message := "ltac2" "message_of_string".

Ltac2 @ external of_int : int -> message := "ltac2" "message_of_int".

Ltac2 @ external of_constr : constr -> message := "ltac2" "message_of_constr".
(** Panics if there is more than one goal under focus. *)

Ltac2 @ external concat : message -> message -> message := "ltac2" "message_concat".
