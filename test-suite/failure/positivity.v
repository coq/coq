(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Negative occurrence *)
Fail Inductive t : Type :=
  c : (t -> nat) -> t.

(* Non-strictely positive occurrence *)
Fail Inductive t : Type :=
  c : ((t -> nat) -> nat) -> t.

(* Self-nested type (no proof of
   soundness yet *)
Fail Inductive t (A:Type) : Type :=
  c : t (t A) -> t A.

(* Nested inductive types *)

Inductive pos (A:Type) :=
  p : pos A -> pos A.

Inductive nnpos (A:Type) :=
  nnp : ((A -> nat) -> nat) -> nnpos A.

Inductive neg (A:Type) :=
  n : (A->neg A) -> neg A.

Inductive arg : Type -> Prop :=
  a : forall A, arg A -> arg A.

(* Strictly covariant parameter: accepted. *)
Fail Fail Inductive t :=
  c : pos t -> t.

(* Non-strictly covariant parameter: not
   strictly positive. *)
Fail Inductive t :=
  c : nnpos t -> t.

(* Contravariant parameter: not positive. *)
Fail Inductive t :=
  c : neg t -> t.

(* Strict index: not positive. *)
Fail Inductive t :=
  c : arg t -> t.
