(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction of [nat] into Ocaml's [int] *)

Require Stdlib.extraction.Extraction.

Require Import Arith EqNat Euclid.
Require Import ExtrOcamlBasic.

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [nat] into [int] is definitively *not* a good idea:

    - This is just a syntactic adaptation, many things can go wrong,
    such as name captures (e.g. if you have a constant named "int"
    in your development, or a module named "Pervasives"). See bug #2878.

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

Extract Inductive nat => int [ "0" "Stdlib.Int.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(** Efficient (but uncertified) versions for usual [nat] functions *)

Extract Constant plus => "(+)".
Extract Constant pred => "fun n -> Stdlib.max 0 (n-1)".
Extract Constant minus => "fun n m -> Stdlib.max 0 (n-m)".
Extract Constant mult => "( * )".
Extract Inlined Constant max => "Stdlib.max".
Extract Inlined Constant min => "Stdlib.min".
(*Extract Inlined Constant nat_beq => "(=)".*)
Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant EqNat.eq_nat_decide => "(=)".

Extract Inlined Constant Peano_dec.eq_nat_dec => "(=)".

Extract Constant Nat.compare =>
 "fun n m -> if n=m then Eq else if n<m then Lt else Gt".
Extract Inlined Constant Compare_dec.leb => "(<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(<=)".
Extract Inlined Constant Compare_dec.lt_dec => "(<)".
Extract Constant Compare_dec.lt_eq_lt_dec =>
 "fun n m -> if n>m then None else Some (n<m)".

Extract Constant Nat.Even_or_Odd => "fun n -> n mod 2 = 0".
Extract Constant Nat.div2 => "fun n -> n/2".

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
