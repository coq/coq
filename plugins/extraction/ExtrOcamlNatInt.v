(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Extraction of [nat] into Ocaml's [int] *)

Require Import Arith Even Div2 EqNat Euclid.
Require Import ExtrOcamlBasic.

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [nat] into [int] is definitively *not* a good idea:

    - Since [int] is bounded while [nat] is (theoretically) infinite,
    you have to make sure by yourself that your program will not
    manipulate numbers greater than [max_int]. Otherwise you should
    consider the translation of [nat] into [big_int].

    - Moreover, the mere translation of [nat] into [int] does not
    change the complexity of functions. For instance, [mult] stays
    quadratic. To mitigate this, we propose here a few efficient (but
    uncertified) realizers for some common functions over [nat].

    This file is hence provided mainly for testing / prototyping
    purpose. For serious use of numbers in extracted programs,
    you are advised to use either coq advanced representations
    (positive, Z, N, BigN, BigZ) or modular/axiomatic representation.
*)


(** Mapping of [nat] into [int]. The last string corresponds to
    a [nat_case], see documentation of [Extract Inductive]. *)

Extract Inductive nat => int [ "0" "succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(** Efficient (but uncertified) versions for usual [nat] functions *)

Extract Constant plus => "(+)".
Extract Constant pred => "fun n -> max 0 (n-1)".
Extract Constant minus => "fun n m -> max 0 (n-m)".
Extract Constant mult => "( * )".
Extract Inlined Constant max => max.
Extract Inlined Constant min => min.
Extract Inlined Constant nat_beq => "(=)".
Extract Inlined Constant EqNat.beq_nat => "(=)".
Extract Inlined Constant EqNat.eq_nat_decide => "(=)".

Extract Inlined Constant Peano_dec.eq_nat_dec => "(=)".

Extract Constant Compare_dec.nat_compare =>
 "fun n m -> if n=m then Eq else if n<m then Lt else Gt".
Extract Inlined Constant Compare_dec.leb => "(<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(<=)".
Extract Constant Compare_dec.lt_eq_lt_dec =>
 "fun n m -> if n>m then None else Some (n<m)".

Extract Constant Even.even_odd_dec => "fun n -> n mod 2 = 0".
Extract Constant Div2.div2 => "fun n -> n/2".

Extract Inductive Euclid.diveucl => "(int * int)" [ "" ].
Extract Constant Euclid.eucl_dev => "fun n m -> (m/n, m mod n)".
Extract Constant Euclid.quotient => "fun n m -> m/n".
Extract Constant Euclid.modulo => "fun n m -> m mod n".

(*
Definition test n m (H:m>0) :=
 let (q,r,_,_) := eucl_dev m H n in
 nat_compare n (q*m+r).

Recursive Extraction test fact.
*)