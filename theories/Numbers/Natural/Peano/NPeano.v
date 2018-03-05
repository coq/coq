(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import PeanoNat Even NAxioms.

(** This file is DEPRECATED ! Use [PeanoNat] (or [Arith]) instead. *)

(** [PeanoNat.Nat] already implements [NAxiomSig] *)

Module Nat <: NAxiomsSig := Nat.

(** Compat notations for stuff that used to be at the beginning of NPeano. *)

Notation leb := Nat.leb (only parsing).
Notation ltb := Nat.ltb (only parsing).
Notation leb_le := Nat.leb_le (only parsing).
Notation ltb_lt := Nat.ltb_lt (only parsing).
Notation pow := Nat.pow (only parsing).
Notation pow_0_r := Nat.pow_0_r (only parsing).
Notation pow_succ_r := Nat.pow_succ_r (only parsing).
Notation square := Nat.square (only parsing).
Notation square_spec := Nat.square_spec (only parsing).
Notation Even := Nat.Even (only parsing).
Notation Odd := Nat.Odd (only parsing).
Notation even := Nat.even (only parsing).
Notation odd := Nat.odd (only parsing).
Notation even_spec := Nat.even_spec (only parsing).
Notation odd_spec := Nat.odd_spec (only parsing).

Lemma Even_equiv n : Even n <-> Even.even n.
Proof. symmetry. apply Even.even_equiv. Qed.
Lemma Odd_equiv n : Odd n <-> Even.odd n.
Proof. symmetry. apply Even.odd_equiv. Qed.

Notation divmod := Nat.divmod (only parsing).
Notation div := Nat.div (only parsing).
Notation modulo := Nat.modulo (only parsing).
Notation divmod_spec := Nat.divmod_spec (only parsing).
Notation div_mod := Nat.div_mod (only parsing).
Notation mod_bound_pos := Nat.mod_bound_pos (only parsing).
Notation sqrt_iter := Nat.sqrt_iter (only parsing).
Notation sqrt := Nat.sqrt (only parsing).
Notation sqrt_iter_spec := Nat.sqrt_iter_spec (only parsing).
Notation sqrt_spec := Nat.sqrt_spec (only parsing).
Notation log2_iter := Nat.log2_iter (only parsing).
Notation log2 := Nat.log2 (only parsing).
Notation log2_iter_spec := Nat.log2_iter_spec (only parsing).
Notation log2_spec := Nat.log2_spec (only parsing).
Notation log2_nonpos := Nat.log2_nonpos (only parsing).
Notation gcd := Nat.gcd (only parsing).
Notation divide := Nat.divide (only parsing).
Notation gcd_divide := Nat.gcd_divide (only parsing).
Notation gcd_divide_l := Nat.gcd_divide_l (only parsing).
Notation gcd_divide_r := Nat.gcd_divide_r (only parsing).
Notation gcd_greatest := Nat.gcd_greatest (only parsing).
Notation testbit := Nat.testbit (only parsing).
Notation shiftl := Nat.shiftl (only parsing).
Notation shiftr := Nat.shiftr (only parsing).
Notation bitwise := Nat.bitwise (only parsing).
Notation land := Nat.land (only parsing).
Notation lor := Nat.lor (only parsing).
Notation ldiff := Nat.ldiff (only parsing).
Notation lxor := Nat.lxor (only parsing).
Notation double_twice := Nat.double_twice (only parsing).
Notation testbit_0_l := Nat.testbit_0_l (only parsing).
Notation testbit_odd_0 := Nat.testbit_odd_0 (only parsing).
Notation testbit_even_0 := Nat.testbit_even_0 (only parsing).
Notation testbit_odd_succ := Nat.testbit_odd_succ (only parsing).
Notation testbit_even_succ := Nat.testbit_even_succ (only parsing).
Notation shiftr_spec := Nat.shiftr_spec (only parsing).
Notation shiftl_spec_high := Nat.shiftl_spec_high (only parsing).
Notation shiftl_spec_low := Nat.shiftl_spec_low (only parsing).
Notation div2_bitwise := Nat.div2_bitwise (only parsing).
Notation odd_bitwise := Nat.odd_bitwise (only parsing).
Notation div2_decr := Nat.div2_decr (only parsing).
Notation testbit_bitwise_1 := Nat.testbit_bitwise_1 (only parsing).
Notation testbit_bitwise_2 := Nat.testbit_bitwise_2 (only parsing).
Notation land_spec := Nat.land_spec (only parsing).
Notation ldiff_spec := Nat.ldiff_spec (only parsing).
Notation lor_spec := Nat.lor_spec (only parsing).
Notation lxor_spec := Nat.lxor_spec (only parsing).

Infix "<=?" := Nat.leb (at level 70) : nat_scope.
Infix "<?" := Nat.ltb (at level 70) : nat_scope.
Infix "^" := Nat.pow : nat_scope.
Infix "/" := Nat.div : nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.
Notation "( x | y )" := (Nat.divide x y) (at level 0) : nat_scope.
