(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Coq.ltac2.Init.

Ltac2 @external make : int -> 'a -> 'a array := "ltac2" "array_make".
Ltac2 @external length : 'a array -> int := "ltac2" "array_length".
Ltac2 @external get : 'a array -> int -> 'a := "ltac2" "array_get".
Ltac2 @external set : 'a array -> int -> 'a -> unit := "ltac2" "array_set".
