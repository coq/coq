(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 @ external print : message -> unit := "ltac2" "print".

Ltac2 @ external of_string : string -> message := "ltac2" "message_of_string".

Ltac2 @ external of_int : int -> message := "ltac2" "message_of_int".

Ltac2 @ external of_ident : ident -> message := "ltac2" "message_of_ident".

Ltac2 @ external of_constr : constr -> message := "ltac2" "message_of_constr".
(** Panics if there is more than one goal under focus. *)

Ltac2 @ external of_exn : exn -> message := "ltac2" "message_of_exn".
(** Panics if there is more than one goal under focus. *)

Ltac2 @ external concat : message -> message -> message := "ltac2" "message_concat".

Module Format.

(** Only for internal use. *)

Ltac2 @ external stop : unit -> ('a, 'b, 'c, 'a) format := "ltac2" "format_stop".

Ltac2 @ external string : ('a, 'b, 'c, 'd) format ->
  (string -> 'a, 'b, 'c, 'd) format := "ltac2" "format_string".

Ltac2 @ external int : ('a, 'b, 'c, 'd) format ->
  (int -> 'a, 'b, 'c, 'd) format := "ltac2" "format_int".

Ltac2 @ external constr : ('a, 'b, 'c, 'd) format ->
  (constr -> 'a, 'b, 'c, 'd) format := "ltac2" "format_constr".

Ltac2 @ external ident : ('a, 'b, 'c, 'd) format ->
  (ident -> 'a, 'b, 'c, 'd) format := "ltac2" "format_ident".

Ltac2 @ external literal : string -> ('a, 'b, 'c, 'd) format ->
  ('a, 'b, 'c, 'd) format := "ltac2" "format_literal".

Ltac2 @ external alpha : ('a, 'b, 'c, 'd) format ->
  (('b -> 'r -> 'c) -> 'r -> 'a, 'b, 'c, 'd) format := "ltac2" "format_alpha".

Ltac2 @ external kfprintf : (message -> 'r) -> ('a, unit, message, 'r) format -> 'a :=
  "ltac2" "format_kfprintf".

End Format.
