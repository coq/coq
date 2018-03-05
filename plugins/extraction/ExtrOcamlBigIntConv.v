(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to Ocaml: conversion from/to [big_int] *)

(** NB: The extracted code should be linked with [nums.cm(x)a]
    from ocaml's stdlib and with the wrapper [big.ml] that
    simplifies the use of [Big_int] (it can be found in the sources
    of Coq). *)

Require Coq.extraction.Extraction.

Require Import Arith ZArith.

Parameter bigint : Type.
Parameter bigint_zero : bigint.
Parameter bigint_succ : bigint -> bigint.
Parameter bigint_opp : bigint -> bigint.
Parameter bigint_twice : bigint -> bigint.

Extract Inlined Constant bigint => "Big.big_int".
Extract Inlined Constant bigint_zero => "Big.zero".
Extract Inlined Constant bigint_succ => "Big.succ".
Extract Inlined Constant bigint_opp => "Big.opp".
Extract Inlined Constant bigint_twice => "Big.double".

Definition bigint_of_nat : nat -> bigint :=
 (fix loop acc n :=
  match n with
   | O => acc
   | S n => loop (bigint_succ acc) n
  end) bigint_zero.

Fixpoint bigint_of_pos p :=
 match p with
  | xH => bigint_succ bigint_zero
  | xO p => bigint_twice (bigint_of_pos p)
  | xI p => bigint_succ (bigint_twice (bigint_of_pos p))
 end.

Fixpoint bigint_of_z z :=
 match z with
  | Z0 => bigint_zero
  | Zpos p => bigint_of_pos p
  | Zneg p => bigint_opp (bigint_of_pos p)
 end.

Fixpoint bigint_of_n n :=
 match n with
  | N0 => bigint_zero
  | Npos p => bigint_of_pos p
 end.

(** NB: as for [pred] or [minus], [nat_of_bigint], [n_of_bigint] and
    [pos_of_bigint] are total and return zero (resp. one) for
    non-positive inputs. *)

Parameter bigint_natlike_rec : forall A, A -> (A->A) -> bigint -> A.
Extract Constant bigint_natlike_rec => "Big.nat_rec".

Definition nat_of_bigint : bigint -> nat := bigint_natlike_rec _ O S.

Parameter bigint_poslike_rec : forall A, (A->A) -> (A->A) -> A -> bigint -> A.
Extract Constant bigint_poslike_rec => "Big.positive_rec".

Definition pos_of_bigint : bigint -> positive := bigint_poslike_rec _ xI xO xH.

Parameter bigint_zlike_case :
 forall A, A -> (bigint->A) -> (bigint->A) -> bigint -> A.
Extract Constant bigint_zlike_case => "Big.z_rec".

Definition z_of_bigint : bigint -> Z :=
 bigint_zlike_case _ Z0 (fun i => Zpos (pos_of_bigint i))
                        (fun i => Zneg (pos_of_bigint i)).

Definition n_of_bigint : bigint -> N :=
 bigint_zlike_case _ N0 (fun i => Npos (pos_of_bigint i)) (fun _ => N0).

(* Tests:

Definition small := 1234%nat.
Definition big := 12345678901234567890%positive.

Definition nat_0 := nat_of_bigint (bigint_of_nat 0).
Definition nat_1 := nat_of_bigint (bigint_of_nat small).
Definition pos_1 := pos_of_bigint (bigint_of_pos 1).
Definition pos_2 := pos_of_bigint (bigint_of_pos big).
Definition n_0 := n_of_bigint (bigint_of_n 0).
Definition n_1 := n_of_bigint (bigint_of_n 1).
Definition n_2 := n_of_bigint (bigint_of_n (Npos big)).
Definition z_0 := z_of_bigint (bigint_of_z 0).
Definition z_1 := z_of_bigint (bigint_of_z 1).
Definition z_2 := z_of_bigint (bigint_of_z (Zpos big)).
Definition z_m1 := z_of_bigint (bigint_of_z (-1)).
Definition z_m2 := z_of_bigint (bigint_of_z (Zneg big)).

Definition test :=
 (nat_0, nat_1, pos_1, pos_2, n_0, n_1, n_2, z_0, z_1, z_2, z_m1, z_m2).
Definition check :=
 (O, small, xH, big, 0%N, 1%N, Npos big, 0%Z, 1%Z, Zpos big, (-1)%Z, Zneg big).

Extraction "/tmp/test.ml" check test.

... and we check that test=check
*)
