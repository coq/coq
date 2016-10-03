(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Declare ML Module "ltac2_plugin".

Global Set Default Proof Mode "Ltac2".

(** Primitive types *)

Ltac2 Type int.
Ltac2 Type string.
Ltac2 Type constr.
Ltac2 Type message.
Ltac2 Type 'a array.

(** Pervasive types *)

Ltac2 Type 'a option := | None | Some ('a).

(** Primitive tactics *)

Module Message.

Ltac2 @ external print : message -> unit := "ltac2" "print".
Ltac2 @ external of_string : string -> message := "ltac2" "message_of_string".
Ltac2 @ external of_int : int -> message := "ltac2" "message_of_int".

End Message.

Module Array.

Ltac2 @external make : int -> 'a -> ('a) array := "ltac2" "array_make".
Ltac2 @external length : ('a) array -> int := "ltac2" "array_length".
Ltac2 @external get : ('a) array -> int -> 'a := "ltac2" "array_get".
Ltac2 @external set : ('a) array -> int -> 'a -> unit := "ltac2" "array_set".

End Array.
