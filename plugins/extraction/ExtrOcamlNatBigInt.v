(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Extraction of [nat] into Ocaml's [big_int] *)

Require Import Arith Even Div2 EqNat Euclid.
Require Import ExtrOcamlBasic.

(** NB: The extracted code should be linked with [nums.(cma|cmxa)]. *)

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [nat] into [big_int] isn't necessarily a good idea.
    See comments in [ExtrOcamlNatInt.v].
*)


(** Mapping of [nat] into [big_int]. The last string corresponds to
    a [nat_case], see documentation of [Extract Inductive]. *)

Extract Inductive nat => "Big_int.big_int"
 [ "Big_int.zero_big_int" "Big_int.succ_big_int" ]
 "(fun fO fS n -> if Big_int.sign_big_int n = 0 then fO () else fS (Big_int.pred_big_int n))".

(** Efficient (but uncertified) versions for usual [nat] functions *)

Extract Constant plus => "Big_int.add_big_int".
Extract Constant mult => "Big_int.mult_big_int".
Extract Constant pred =>
 "fun n -> Big_int.max_big_int Big_int.zero_big_int (Big_int.pred_big_int n)".
Extract Constant minus =>
 "fun n m -> Big_int.max_big_int Big_int.zero_big_int (Big_int.sub_big_int n m)".
Extract Constant max => "Big_int.max_big_int".
Extract Constant min => "Big_int.min_big_int".
Extract Constant nat_beq => "Big_int.eq_big_int".
Extract Constant EqNat.beq_nat => "Big_int.eq_big_int".
Extract Constant EqNat.eq_nat_decide => "Big_int.eq_big_int".

Extract Inlined Constant Peano_dec.eq_nat_dec => "Big_int.eq_big_int".

Extract Constant Compare_dec.nat_compare =>
"fun n m ->
 let s = Big_int.compare_big_int n m in
 if s=0 then Eq else if s<0 then Lt else Gt".

Extract Inlined Constant Compare_dec.leb => "Big_int.le_big_int".
Extract Inlined Constant Compare_dec.le_lt_dec => "Big_int.le_big_int".
Extract Constant Compare_dec.lt_eq_lt_dec =>
"fun n m ->
 let s = Big_int.sign_big_int n m in
 if s>0 then None else Some (s<0)".

Extract Constant Even.even_odd_dec =>
 "fun n -> Big_int.sign_big_int (Big_int.mod_big_int n (Big_int.big_int_of_int 2)) = 0".
Extract Constant Div2.div2 =>
 "fun n -> Big_int.div_big_int n (Big_int.big_int_of_int 2)".

Extract Inductive Euclid.diveucl => "(Big_int.big_int * Big_int.big_int)" [""].
Extract Constant Euclid.eucl_dev => "fun n m -> Big_int.quomod_big_int m n".
Extract Constant Euclid.quotient => "fun n m -> Big_int.div_big_int m n".
Extract Constant Euclid.modulo => "fun n m -> Big_int.mod_big_int m n".

(*
Definition test n m (H:m>0) :=
 let (q,r,_,_) := eucl_dev m H n in
 nat_compare n (q*m+r).

Recursive Extraction test fact.
*)
