(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction of [nat] into Zarith's [Z.t] *)

Require Stdlib.extraction.Extraction.

Require Import Arith EqNat Euclid.
Require Import ExtrOcamlBasic.

(** NB: The extracted code depends on [zarith] package. *)

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [nat] into [big_int] isn't necessarily a good idea.
    See comments in [ExtrOcamlNatInt.v].
*)


(** Mapping of [nat] into [big_int].
    See documentation of [Extract Inductive]. *)

Extract Inductive nat => "Big_int_Z.big_int"
 [ "Big_int_Z.zero_big_int" "Big_int_Z.succ_big_int" ]
 "(fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))".

(** Efficient (but uncertified) versions for usual [nat] functions *)

Extract Constant plus => "Big_int_Z.add_big_int".
Extract Constant mult => "Big_int_Z.mult_big_int".
Extract Constant pred =>
 "(fun n -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.pred_big_int n))".
Extract Constant minus =>
 "(fun n m -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.sub_big_int n m))".
Extract Constant max => "Big_int_Z.max_big_int".
Extract Constant min => "Big_int_Z.min_big_int".
(*Extract Constant nat_beq => "Big.eq".*)
Extract Constant Nat.eqb => "Big_int_Z.eq_big_int".
Extract Constant EqNat.eq_nat_decide => "Big_int_Z.eq_big_int".

Extract Constant Peano_dec.eq_nat_dec => "Big_int_Z.eq_big_int".

Extract Constant Nat.compare =>
 "(fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)".

Extract Constant Compare_dec.leb => "Big_int_Z.le_big_int".
Extract Constant Compare_dec.le_lt_dec => "Big_int_Z.le_big_int".
Extract Constant Compare_dec.lt_eq_lt_dec =>
 "(fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then (Some false) else if s < 0 then (Some true) else None)".

Extract Constant Nat.Even_or_Odd =>
 "(fun n -> Big_int_Z.sign_big_int
  (Big_int_Z.mod_big_int n (Big_int_Z.big_int_of_int 2)) = 0)".
Extract Constant Nat.div2 => "(fun n -> Big_int_Z.div_big_int n (Big_int_Z.big_int_of_int 2))".

Extract Inductive Euclid.diveucl => "(Big_int_Z.big_int * Big_int_Z.big_int)" [""].
Extract Constant Euclid.eucl_dev => "(fun n m -> Big_int_Z.quomod_big_int m n)".
Extract Constant Euclid.quotient => "(fun n m -> Big_int_Z.div_big_int m n)".
Extract Constant Euclid.modulo => "(fun n m -> Big_int_Z.mod_big_int m n)".

(*
Require Import Euclid.
Definition test n m (H:m>0) :=
 let (q,r,_,_) := eucl_dev m H n in
 nat_compare n (q*m+r).

Extraction "/tmp/test.ml" test fact pred minus max min Div2.div2.
*)
