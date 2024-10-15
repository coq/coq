(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export CarryType.

Register bool as kernel.ind_bool.
Register prod as kernel.ind_pair.
Register carry as kernel.ind_carry.
Register comparison as kernel.ind_cmp.

Primitive int := #int63_type.
Register int as num.int63.type.
Variant pos_neg_int63 := Pos (d:int) | Neg (d:int).
Register pos_neg_int63 as num.int63.pos_neg_int63.
Declare Scope uint63_scope.
Definition id_int : int -> int := fun x => x.
Record int_wrapper := wrap_int {int_wrap : int}.
Register int_wrapper as num.int63.int_wrapper.
Register wrap_int as num.int63.wrap_int.
Definition printer (x : int_wrapper) : pos_neg_int63 := Pos (int_wrap x).
Definition parser (x : pos_neg_int63) : option int :=
  match x with
  | Pos p => Some p
  | Neg _ => None
  end.


Declare Scope int63_scope.
Module Import Int63NotationsInternalA.
Delimit Scope int63_scope with int63.
End Int63NotationsInternalA.
Number Notation int parser printer : int63_scope.

Module Import Uint63NotationsInternalA.
Delimit Scope uint63_scope with uint63.
Bind Scope uint63_scope with int.
End Uint63NotationsInternalA.
Number Notation int parser printer : uint63_scope.


(* Logical operations *)
Primitive lsl := #int63_lsl.

Primitive lsr := #int63_lsr.

Primitive land := #int63_land.

Primitive lor := #int63_lor.

Primitive lxor := #int63_lxor.


Primitive asr := #int63_asr.

(* Arithmetic modulo operations *)
Primitive add := #int63_add.

Primitive sub := #int63_sub.

Primitive mul := #int63_mul.

Primitive mulc := #int63_mulc.

Primitive div := #int63_div.

Primitive mod := #int63_mod.

Primitive divs := #int63_divs.

Primitive mods := #int63_mods.

(* Comparisons *)
Primitive eqb := #int63_eq.
Register eqb as num.int63.eqb.

Primitive ltb := #int63_lt.

Primitive leb := #int63_le.

Primitive ltsb := #int63_lts.

Primitive lesb := #int63_les.

(** Exact arithmetic operations *)

Primitive addc := #int63_addc.

Primitive addcarryc := #int63_addcarryc.

Primitive subc := #int63_subc.

Primitive subcarryc := #int63_subcarryc.

Primitive diveucl := #int63_diveucl.

Primitive diveucl_21 := #int63_div21.

Primitive addmuldiv := #int63_addmuldiv.

(** Comparison *)
Primitive compare := #int63_compare.

Primitive compares := #int63_compares.

(** Exotic operations *)

Primitive head0 := #int63_head0.
Primitive tail0 := #int63_tail0.

Module Export PrimInt63Notations.
  Export Int63NotationsInternalA.
  Export Uint63NotationsInternalA.
End PrimInt63Notations.
