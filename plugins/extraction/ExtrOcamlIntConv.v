(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction to Ocaml: conversion from/to [int]

    Nota: no check that [int] values aren't generating overflows *)

Require Coq.extraction.Extraction.

Require Import Arith ZArith.

Parameter int : Type.
Parameter int_zero : int.
Parameter int_succ : int -> int.
Parameter int_opp : int -> int.
Parameter int_twice : int -> int.

Extract Inlined Constant int => int.
Extract Inlined Constant int_zero => "0".
Extract Inlined Constant int_succ => "succ".
Extract Inlined Constant int_opp => "-".
Extract Inlined Constant int_twice => "2 *".

Definition int_of_nat : nat -> int :=
 (fix loop acc n :=
  match n with
   | O => acc
   | S n => loop (int_succ acc) n
  end) int_zero.

Fixpoint int_of_pos p :=
 match p with
  | xH => int_succ int_zero
  | xO p => int_twice (int_of_pos p)
  | xI p => int_succ (int_twice (int_of_pos p))
 end.

Fixpoint int_of_z z :=
 match z with
  | Z0 => int_zero
  | Zpos p => int_of_pos p
  | Zneg p => int_opp (int_of_pos p)
 end.

Fixpoint int_of_n n :=
 match n with
  | N0 => int_zero
  | Npos p => int_of_pos p
 end.

(** NB: as for [pred] or [minus], [nat_of_int], [n_of_int] and
    [pos_of_int] are total and return zero (resp. one) for
    non-positive inputs. *)

Parameter int_natlike_rec : forall A, A -> (A->A) -> int -> A.
Extract Constant int_natlike_rec =>
"fun fO fS ->
 let rec loop acc i = if i <= 0 then acc else loop (fS acc) (i-1)
 in loop fO".

Definition nat_of_int : int -> nat := int_natlike_rec _ O S.

Parameter int_poslike_rec : forall A, A -> (A->A) -> (A->A) -> int -> A.
Extract Constant int_poslike_rec =>
"fun f1 f2x f2x1 ->
 let rec loop i = if i <= 1 then f1 else
  if i land 1 = 0 then f2x (loop (i lsr 1)) else f2x1 (loop (i lsr 1))
 in loop".

Definition pos_of_int : int -> positive := int_poslike_rec _ xH xO xI.

Parameter int_zlike_case : forall A, A -> (int->A) -> (int->A) -> int -> A.
Extract Constant int_zlike_case =>
"fun f0 fpos fneg i ->
 if i = 0 then f0 else if i>0 then fpos i else fneg (-i)".

Definition z_of_int : int -> Z :=
 int_zlike_case _ Z0 (fun i => Zpos (pos_of_int i))
                     (fun i => Zneg (pos_of_int i)).

Definition n_of_int : int -> N :=
 int_zlike_case _ N0 (fun i => Npos (pos_of_int i)) (fun _ => N0).

(** Warning: [z_of_int] is currently wrong for Ocaml's [min_int],
    since [min_int] has no positive opposite ([-min_int = min_int]).
*)

(*
Extraction "/tmp/test.ml"
  nat_of_int int_of_nat
  pos_of_int int_of_pos
  z_of_int int_of_z
  n_of_int int_of_n.
*)
