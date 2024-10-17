(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

From Stdlib Require Import BinNums PosDef IntDef.
From Stdlib Require Export PrimInt63 Uint63Axioms.

Local Open Scope Z_scope.

Local Notation "2" := (Zpos 2) : Z_scope.
Local Infix "^" := Z.pow : Z_scope.
Local Notation "x <= y" := (Z.compare x y <> Gt) : Z_scope.
Local Notation "x < y" := (Z.compare x y = Lt) : Z_scope.

Definition min_int := Eval vm_compute in (lsl 1 62).

(** Translation to and from Z *)
Definition to_Z (i : int) :=
  if ltb i min_int then to_Z i
  else Z.opp (to_Z (sub 0 i)).

(** Specification of operations that differ on signed and unsigned ints *)

Axiom asr_spec : forall x p, to_Z (asr x p) = Z.div (to_Z x) (2 ^ (to_Z p)).

Axiom div_spec : forall x y,
    to_Z x <> to_Z min_int \/ to_Z y <> Zneg 1 ->
  to_Z (divs x y) = Z.quot (to_Z x) (to_Z y).

Axiom mod_spec : forall x y, to_Z (mods x y) = Z.rem (to_Z x) (to_Z y).

Axiom ltb_spec : forall x y, ltsb x y = true <-> to_Z x < to_Z y.

Axiom leb_spec : forall x y, lesb x y = true <-> to_Z x <= to_Z y.

Axiom compare_spec : forall x y, compares x y = Z.compare (to_Z x) (to_Z y).
