(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Extraction to Ocaml: conversion from/to [big_int] *)

(** The extracted code should be linked with [nums.(cma|cmxa)] *)

Require Import Arith ZArith.

Parameter bigint : Type.
Parameter bigint_zero : bigint.
Parameter bigint_succ : bigint -> bigint.
Parameter bigint_opp : bigint -> bigint.
Parameter bigint_twice : bigint -> bigint.

Extract Inlined Constant bigint => "Big_int.big_int".
Extract Inlined Constant bigint_zero => "Big_int.zero_big_int".
Extract Inlined Constant bigint_succ => "Big_int.succ_big_int".
Extract Inlined Constant bigint_opp => "Big_int.minus_big_int".
Extract Inlined Constant bigint_twice => "Big_int.mult_int_big_int 2".

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
Extract Constant bigint_natlike_rec =>
"fun fO fS ->
 let rec loop acc i = if Big_int.sign_big_int i <= 0 then acc
  else loop (fS acc) (Big_int.pred_big_int i)
 in loop fO".

Definition nat_of_bigint : bigint -> nat := bigint_natlike_rec _ O S.

Parameter bigint_poslike_rec : forall A, A -> (A->A) -> (A->A) -> bigint -> A.
Extract Constant bigint_poslike_rec =>
"fun f1 f2x f2x1 ->
 let rec loop i = if Big_int.le_big_int i Big_int.unit_big_int then f1
 else
  let (q,r) = Big_int.quomod_big_int i (Big_int.big_int_of_int 2) in
  if Big_int.sign_big_int r = 0 then f2x (loop q) else f2x1 (loop q)
 in loop".

Definition pos_of_bigint : bigint -> positive := bigint_poslike_rec _ xH xO xI.

Parameter bigint_zlike_case : forall A, A -> (bigint->A) -> (bigint->A) -> bigint -> A.
Extract Constant bigint_zlike_case =>
"fun f0 fpos fneg i ->
  let sgn = Big_int.sign_big_int i in
  if sgn = 0 then f0 else if sgn>0 then fpos i
  else fneg (Big_int.minus_big_int i)".

Definition z_of_bigint : bigint -> Z :=
 bigint_zlike_case _ Z0 (fun i => Zpos (pos_of_bigint i))
                     (fun i => Zneg (pos_of_bigint i)).

Definition n_of_bigint : bigint -> N :=
 bigint_zlike_case _ N0 (fun i => Npos (pos_of_bigint i)) (fun _ => N0).

(*
Extraction "/tmp/test.ml"
  nat_of_bigint bigint_of_nat
  pos_of_bigint bigint_of_pos
  z_of_bigint bigint_of_z
  n_of_bigint bigint_of_n.
*)