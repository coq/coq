(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import PeanoNat Even NAxioms.

(** This file is DEPRECATED ! Use [PeanoNat] (or [Arith]) instead. *)

(** [PeanoNat.Nat] already implements [NAxiomSig] *)

Module Nat <: NAxiomsSig := Nat.

(** Compat notations for stuff that used to be at the beginning of NPeano. *)

Notation leb := Nat.leb (compat "8.4").
Notation ltb := Nat.ltb (compat "8.4").
Notation leb_le := Nat.leb_le (compat "8.4").
Notation ltb_lt := Nat.ltb_lt (compat "8.4").
Notation pow := Nat.pow (compat "8.4").
Notation pow_0_r := Nat.pow_0_r (compat "8.4").
Notation pow_succ_r := Nat.pow_succ_r (compat "8.4").
Notation square := Nat.square (compat "8.4").
Notation square_spec := Nat.square_spec (compat "8.4").
Notation Even := Nat.Even (compat "8.4").
Notation Odd := Nat.Odd (compat "8.4").
Notation even := Nat.even (compat "8.4").
Notation odd := Nat.odd (compat "8.4").
Notation even_spec := Nat.even_spec (compat "8.4").
Notation odd_spec := Nat.odd_spec (compat "8.4").

Lemma Even_equiv n : Even n <-> Even.even n.
Proof. symmetry. apply Even.even_equiv. Qed.
Lemma Odd_equiv n : Odd n <-> Even.odd n.
Proof. symmetry. apply Even.odd_equiv. Qed.

Notation divmod := Nat.divmod (compat "8.4").
Notation div := Nat.div (compat "8.4").
Notation modulo := Nat.modulo (compat "8.4").
Notation divmod_spec := Nat.divmod_spec (compat "8.4").
Notation div_mod := Nat.div_mod (compat "8.4").
Notation mod_bound_pos := Nat.mod_bound_pos (compat "8.4").
Notation sqrt_iter := Nat.sqrt_iter (compat "8.4").
Notation sqrt := Nat.sqrt (compat "8.4").
Notation sqrt_iter_spec := Nat.sqrt_iter_spec (compat "8.4").
Notation sqrt_spec := Nat.sqrt_spec (compat "8.4").
Notation log2_iter := Nat.log2_iter (compat "8.4").
Notation log2 := Nat.log2 (compat "8.4").
Notation log2_iter_spec := Nat.log2_iter_spec (compat "8.4").
Notation log2_spec := Nat.log2_spec (compat "8.4").
Notation log2_nonpos := Nat.log2_nonpos (compat "8.4").
Notation gcd := Nat.gcd (compat "8.4").
Notation divide := Nat.divide (compat "8.4").
Notation gcd_divide := Nat.gcd_divide (compat "8.4").
Notation gcd_divide_l := Nat.gcd_divide_l (compat "8.4").
Notation gcd_divide_r := Nat.gcd_divide_r (compat "8.4").
Notation gcd_greatest := Nat.gcd_greatest (compat "8.4").
Notation testbit := Nat.testbit (compat "8.4").
Notation shiftl := Nat.shiftl (compat "8.4").
Notation shiftr := Nat.shiftr (compat "8.4").
Notation bitwise := Nat.bitwise (compat "8.4").
Notation land := Nat.land (compat "8.4").
Notation lor := Nat.lor (compat "8.4").
Notation ldiff := Nat.ldiff (compat "8.4").
Notation lxor := Nat.lxor (compat "8.4").
Notation double_twice := Nat.double_twice (compat "8.4").
Notation testbit_0_l := Nat.testbit_0_l (compat "8.4").
Notation testbit_odd_0 := Nat.testbit_odd_0 (compat "8.4").
Notation testbit_even_0 := Nat.testbit_even_0 (compat "8.4").
Notation testbit_odd_succ := Nat.testbit_odd_succ (compat "8.4").
Notation testbit_even_succ := Nat.testbit_even_succ (compat "8.4").
Notation shiftr_spec := Nat.shiftr_spec (compat "8.4").
Notation shiftl_spec_high := Nat.shiftl_spec_high (compat "8.4").
Notation shiftl_spec_low := Nat.shiftl_spec_low (compat "8.4").
Notation div2_bitwise := Nat.div2_bitwise (compat "8.4").
Notation odd_bitwise := Nat.odd_bitwise (compat "8.4").
Notation div2_decr := Nat.div2_decr (compat "8.4").
Notation testbit_bitwise_1 := Nat.testbit_bitwise_1 (compat "8.4").
Notation testbit_bitwise_2 := Nat.testbit_bitwise_2 (compat "8.4").
Notation land_spec := Nat.land_spec (compat "8.4").
Notation ldiff_spec := Nat.ldiff_spec (compat "8.4").
Notation lor_spec := Nat.lor_spec (compat "8.4").
Notation lxor_spec := Nat.lxor_spec (compat "8.4").

Infix "<=?" := Nat.leb (at level 70) : nat_scope.
Infix "<?" := Nat.ltb (at level 70) : nat_scope.
Infix "^" := Nat.pow : nat_scope.
Infix "/" := Nat.div : nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.
Notation "( x | y )" := (Nat.divide x y) (at level 0) : nat_scope.
