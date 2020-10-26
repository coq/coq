(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
Declare Scope int63_scope.
Definition id_int : int -> int := fun x => x.
Declare ML Module "int63_syntax_plugin".

Module Export Int63NotationsInternalA.
Delimit Scope int63_scope with int63.
Bind Scope int63_scope with int.
End Int63NotationsInternalA.

(* Logical operations *)
Primitive lsl := #int63_lsl.

Primitive lsr := #int63_lsr.

Primitive land := #int63_land.

Primitive lor := #int63_lor.

Primitive lxor := #int63_lxor.

(* Arithmetic modulo operations *)
Primitive add := #int63_add.

Primitive sub := #int63_sub.

Primitive mul := #int63_mul.

Primitive mulc := #int63_mulc.

Primitive div := #int63_div.

Primitive mod := #int63_mod.

(* Comparisons *)
Primitive eqb := #int63_eq.

Primitive ltb := #int63_lt.

Primitive leb := #int63_le.

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

(** Exotic operations *)

Primitive head0 := #int63_head0.
Primitive tail0 := #int63_tail0.
