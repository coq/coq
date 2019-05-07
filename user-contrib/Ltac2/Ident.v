(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 Type t := ident.

Ltac2 @ external equal : t -> t -> bool := "ltac2" "ident_equal".

Ltac2 @ external of_string : string -> t option := "ltac2" "ident_of_string".

Ltac2 @ external to_string : t -> string := "ltac2" "ident_to_string".
