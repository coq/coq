(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)

Require ssreflect.

Axiom add_comm : forall a b, a + b = b + a.

Goal (forall a b, a + b = b + a).
intros.
rewrite add_comm, add_comm.
split.
Abort.

Module Foo.
Import ssreflect.

Goal (forall a b, a + b = b + a).
intros.
rewrite 2![_ + _]add_comm.
split.
Abort.
End Foo.

Goal (forall a b, a + b = b + a).
intros.
rewrite add_comm, add_comm.
split.
Abort.
