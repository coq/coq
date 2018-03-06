(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction of [nat] into Ocaml's [big_int] *)

Require Coq.extraction.Extraction.

Require Import Arith Even Div2 EqNat Euclid.
Require Import ExtrOcamlBasic.

(** NB: The extracted code should be linked with [nums.cm(x)a]
    from ocaml's stdlib and with the wrapper [big.ml] that
    simplifies the use of [Big_int] (it can be found in the sources
    of Coq). *)

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [nat] into [big_int] isn't necessarily a good idea.
    See comments in [ExtrOcamlNatInt.v].
*)


(** Mapping of [nat] into [big_int]. The last string corresponds to
    a [nat_case], see documentation of [Extract Inductive]. *)

Extract Inductive nat => "Big.big_int" [ "Big.zero" "Big.succ" ]
 "Big.nat_case".

(** Efficient (but uncertified) versions for usual [nat] functions *)

Extract Constant plus => "Big.add".
Extract Constant mult => "Big.mult".
Extract Constant pred => "fun n -> Big.max Big.zero (Big.pred n)".
Extract Constant minus => "fun n m -> Big.max Big.zero (Big.sub n m)".
Extract Constant max => "Big.max".
Extract Constant min => "Big.min".
(*Extract Constant nat_beq => "Big.eq".*)
Extract Constant EqNat.beq_nat => "Big.eq".
Extract Constant EqNat.eq_nat_decide => "Big.eq".

Extract Constant Peano_dec.eq_nat_dec => "Big.eq".

Extract Constant Nat.compare =>
 "Big.compare_case Eq Lt Gt".

Extract Constant Compare_dec.leb => "Big.le".
Extract Constant Compare_dec.le_lt_dec => "Big.le".
Extract Constant Compare_dec.lt_eq_lt_dec =>
 "Big.compare_case (Some false) (Some true) None".

Extract Constant Even.even_odd_dec =>
 "fun n -> Big.sign (Big.mod n Big.two) = 0".
Extract Constant Div2.div2 => "fun n -> Big.div n Big.two".

Extract Inductive Euclid.diveucl => "(Big.big_int * Big.big_int)" [""].
Extract Constant Euclid.eucl_dev => "fun n m -> Big.quomod m n".
Extract Constant Euclid.quotient => "fun n m -> Big.div m n".
Extract Constant Euclid.modulo => "fun n m -> Big.modulo m n".

(*
Require Import Euclid.
Definition test n m (H:m>0) :=
 let (q,r,_,_) := eucl_dev m H n in
 nat_compare n (q*m+r).

Extraction "/tmp/test.ml" test fact pred minus max min Div2.div2.
*)
