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
Ltac2 Type char.

Ltac2 Type evar.
Ltac2 Type constr.
Ltac2 Type ident.
Ltac2 Type message.
Ltac2 Type exn := [ .. ].
Ltac2 Type 'a array.

(** Pervasive types *)

Ltac2 Type 'a option := [ None | Some ('a) ].

Ltac2 Type 'a ref := { mutable contents : 'a }.

Ltac2 Type bool := [ true | false ].
