(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extraction of [positive], [N], and [Z], into Zarith's [Z.t] *)

Require Stdlib.extraction.Extraction.

Require Import ZArith NArith.
Require Import ExtrOcamlBasic.

Extraction Blacklist Z Big_int_Z.

(** NB: The extracted code depends on [zarith] package. *)

(** Disclaimer: trying to obtain efficient certified programs
    by extracting [Z] into [big_int] isn't necessarily a good idea.
    See the Disclaimer in [ExtrOcamlNatInt]. *)

(** Mapping of [positive], [Z], [N] into [Z]. The last strings
    emulate the matching, see documentation of [Extract Inductive]. *)

Extract Inductive positive => "Big_int_Z.big_int"
 [ "(fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x))"
   "Big_int_Z.mult_int_big_int 2" "Big_int_Z.unit_big_int" ]
 "(fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)".

Extract Inductive Z => "Big_int_Z.big_int"
 [ "Big_int_Z.zero_big_int" "" "Big_int_Z.minus_big_int" ]
 "(fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in
  if s = 0 then fO () else if s > 0 then fp z
  else fn (Big_int_Z.minus_big_int z))".

Extract Inductive N => "Big_int_Z.big_int"
 [ "Big_int_Z.zero_big_int" "" ]
 "(fun fO fp n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fp n)".

(** Nota: the "" above is used as an identity function "(fun p->p)" *)

(** Efficient (but uncertified) versions for usual functions *)

Extract Constant Pos.add => "Big_int_Z.add_big_int".
Extract Constant Pos.succ => "Big_int_Z.succ_big_int".
Extract Constant Pos.pred =>
 "(fun n -> Big_int_Z.max_big_int Big_int_Z.unit_big_int
  (Big_int_Z.pred_big_int n))".
Extract Constant Pos.sub =>
 "(fun n m -> Big_int_Z.max_big_int
  Big_int_Z.unit_big_int (Big_int_Z.sub_big_int n m))".
Extract Constant Pos.mul => "Big_int_Z.mult_big_int".
Extract Constant Pos.min => "Big_int_Z.min_big_int".
Extract Constant Pos.max => "Big_int_Z.max_big_int".
Extract Constant Pos.compare =>
 "(fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)".
Extract Constant Pos.compare_cont =>
 "(fun c x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then c else if s < 0 then Lt else Gt)".

Extract Constant N.add => "Big_int_Z.add_big_int".
Extract Constant N.succ => "Big_int_Z.succ_big_int".
Extract Constant N.pred =>
 "(fun n -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.pred_big_int n))".
Extract Constant N.sub =>
 "(fun n m -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.sub_big_int n m))".
Extract Constant N.mul => "Big_int_Z.mult_big_int".
Extract Constant N.min => "Big_int_Z.min_big_int".
Extract Constant N.max => "Big_int_Z.max_big_int".
Extract Constant N.div_eucl =>
  "Big_int_Z.(fun x y ->
    if eq_big_int zero_big_int y then (zero_big_int, x) else
    quomod_big_int x y)".
Extract Constant N.div =>
 "(fun a b -> if Big_int_Z.eq_big_int b Big_int_Z.zero_big_int
  then Big_int_Z.zero_big_int else Big_int_Z.div_big_int a b)".
Extract Constant N.modulo =>
 "(fun a b -> if Big_int_Z.eq_big_int b Big_int_Z.zero_big_int
  then a else Big_int_Z.mod_big_int a b)".
Extract Constant Z.eqb => "Big_int_Z.eq_big_int".
Extract Constant Z.eq_dec => "Big_int_Z.eq_big_int".
Extract Constant N.compare =>
 "(fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)".

(* In Zarith, the second operand of a shift is an [int].
   The conversion to [int] may throw an [Overflow].
   Bigger shifts involve enormous numbers that don't fit in memory anyway. *)
Extract Constant N.shiftl => "Big_int_Z.(fun x y -> shift_left_big_int x (int_of_big_int y))".
Extract Constant N.shiftr => "Big_int_Z.(fun x y -> shift_right_big_int x (int_of_big_int y))".

Extract Constant Z.add => "Big_int_Z.add_big_int".
Extract Constant Z.succ => "Big_int_Z.succ_big_int".
Extract Constant Z.pred => "Big_int_Z.pred_big_int".
Extract Constant Z.sub => "Big_int_Z.sub_big_int".
Extract Constant Z.mul => "Big_int_Z.mult_big_int".
Extract Constant Z.opp => "Big_int_Z.minus_big_int".
Extract Constant Z.abs => "Big_int_Z.abs_big_int".
Extract Constant Z.min => "Big_int_Z.min_big_int".
Extract Constant Z.max => "Big_int_Z.max_big_int".
Extract Constant Z.compare =>
 "(fun x y -> let s = Big_int_Z.compare_big_int x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)".

Extract Constant Z.eqb => "Big_int_Z.eq_big_int".
Extract Constant Z.eq_dec => "Big_int_Z.eq_big_int".
Extract Constant Z.to_N => "Big_int_Z.(fun p -> if sign_big_int p < 0 then zero_big_int else p)".
Extract Constant Z.of_N => "(fun p -> p)".
Extract Constant Z.abs_N => "Big_int_Z.abs_big_int".

Extract Constant Z.div_eucl => "Big_int_Z.(fun x y ->
  match sign_big_int y with
  | 0 -> (zero_big_int, x)
  | 1 -> quomod_big_int x y
  | _ -> let (q, r) = quomod_big_int (add_int_big_int (-1) x) y in
          (add_int_big_int (-1) q, add_big_int (add_int_big_int 1 y) r))".
Extract Constant Z.div => "Big_int_Z.(fun x y ->
  match sign_big_int y with
  | 0 -> zero_big_int
  | 1 -> div_big_int x y
  | _ -> add_int_big_int (-1) (div_big_int (add_int_big_int (-1) x) y))".
Extract Constant Z.modulo => "Big_int_Z.(fun x y ->
  match sign_big_int y with
  | 0 -> x
  | 1 -> mod_big_int x y
  | _ -> add_big_int y (add_int_big_int 1 (mod_big_int (add_int_big_int (-1) x) y)))".

Extract Constant Z.shiftl => "Big_int_Z.(fun x y ->
  let y = int_of_big_int y in
  if y < 0 then shift_right_big_int x (-y)
  else shift_left_big_int x y)".
Extract Constant Z.shiftr => "Big_int_Z.(fun x y ->
  let y = int_of_big_int y in
  if y < 0 then shift_left_big_int x (-y)
  else shift_right_big_int x y)".

(** Test:
Require Import ZArith NArith.

Extraction "/tmp/test.ml"
 Pos.add Pos.pred Pos.sub Pos.mul Pos.compare N.pred N.sub N.div N.modulo N.compare
 Z.add Z.mul Z.compare Z.of_N Z.abs_N Z.div Z.modulo.
*)
