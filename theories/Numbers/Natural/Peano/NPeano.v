(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import PeanoNat NAxioms.

(** This file is DEPRECATED ! Use [PeanoNat] (or [Arith]) instead. *)

(** [PeanoNat.Nat] already implements [NAxiomSig] *)

Module Nat <: NAxiomsSig := Nat.

(** Compat notations for stuff that used to be at the beginning of NPeano. *)

#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.leb instead.")]
Notation leb := Nat.leb (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.ltb instead.")]
Notation ltb := Nat.ltb (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.leb_le instead.")]
Notation leb_le := Nat.leb_le (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.ltb_lt instead.")]
Notation ltb_lt := Nat.ltb_lt (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.pow instead.")]
Notation pow := Nat.pow (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.pow_0_r instead.")]
Notation pow_0_r := Nat.pow_0_r (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.pow_succ_r instead.")]
Notation pow_succ_r := Nat.pow_succ_r (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.square instead.")]
Notation square := Nat.square (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.square_rec instead.")]
Notation square_spec := Nat.square_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.Even instead.")]
Notation Even := Nat.Even (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.Odd instead.")]
Notation Odd := Nat.Odd (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.even instead.")]
Notation even := Nat.even (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.odd instead.")]
Notation odd := Nat.odd (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.even_spec instead.")]
Notation even_spec := Nat.even_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.odd_spec instead.")]
Notation odd_spec := Nat.odd_spec (only parsing).

#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.divmod instead.")]
Notation divmod := Nat.divmod (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.div instead.")]
Notation div := Nat.div (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.modulo instead.")]
Notation modulo := Nat.modulo (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.divmod_spec instead.")]
Notation divmod_spec := Nat.divmod_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.mod_bound_pos instead.")]
Notation mod_bound_pos := Nat.mod_bound_pos (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.sqrt_iter instead.")]
Notation sqrt_iter := Nat.sqrt_iter (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.sqrt instead.")]
Notation sqrt := Nat.sqrt (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.sqrt_iter_spec instead.")]
Notation sqrt_iter_spec := Nat.sqrt_iter_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.sqrt_spec instead.")]
Notation sqrt_spec := Nat.sqrt_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.log2_iter instead.")]
Notation log2_iter := Nat.log2_iter (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.log2 instead.")]
Notation log2 := Nat.log2 (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.log2_iter_spec instead.")]
Notation log2_iter_spec := Nat.log2_iter_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.log2_spec instead.")]
Notation log2_spec := Nat.log2_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.log2_nonpos instead.")]
Notation log2_nonpos := Nat.log2_nonpos (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.gcd instead.")]
Notation gcd := Nat.gcd (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.divide instead.")]
Notation divide := Nat.divide (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.gcd_divide instead.")]
Notation gcd_divide := Nat.gcd_divide (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.gcd_divide_l instead.")]
Notation gcd_divide_l := Nat.gcd_divide_l (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.gcd_divide_r instead.")]
Notation gcd_divide_r := Nat.gcd_divide_r (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.gcd_greatest instead.")]
Notation gcd_greatest := Nat.gcd_greatest (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.testbit instead.")]
Notation testbit := Nat.testbit (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.shiftl instead.")]
Notation shiftl := Nat.shiftl (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.shiftr instead.")]
Notation shiftr := Nat.shiftr (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.bitwise instead.")]
Notation bitwise := Nat.bitwise (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.land instead.")]
Notation land := Nat.land (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.lor instead.")]
Notation lor := Nat.lor (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.ldiff instead.")]
Notation ldiff := Nat.ldiff (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.lxor instead.")]
Notation lxor := Nat.lxor (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.double_twice instead.")]
Notation double_twice := Nat.double_twice (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.testbit_0_l instead.")]
Notation testbit_0_l := Nat.testbit_0_l (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.testbit_odd_0 instead.")]
Notation testbit_odd_0 := Nat.testbit_odd_0 (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.testbit_even_0 instead.")]
Notation testbit_even_0 := Nat.testbit_even_0 (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.testbit_odd_succ instead.")]
Notation testbit_odd_succ := Nat.testbit_odd_succ (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.testbit_even_succ instead.")]
Notation testbit_even_succ := Nat.testbit_even_succ (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.shiftr_spec instead.")]
Notation shiftr_spec := Nat.shiftr_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.shiftr_spec_high instead.")]
Notation shiftl_spec_high := Nat.shiftl_spec_high (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.shiftr_spec_low instead.")]
Notation shiftl_spec_low := Nat.shiftl_spec_low (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.div2_bitwise instead.")]
Notation div2_bitwise := Nat.div2_bitwise (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.odd_bitwise instead.")]
Notation odd_bitwise := Nat.odd_bitwise (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.div2_decr instead.")]
Notation div2_decr := Nat.div2_decr (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.testbit_bitwise_1 instead.")]
Notation testbit_bitwise_1 := Nat.testbit_bitwise_1 (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.testbit_bitwise_2 instead.")]
Notation testbit_bitwise_2 := Nat.testbit_bitwise_2 (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.land_spec instead.")]
Notation land_spec := Nat.land_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.ldiff_spec instead.")]
Notation ldiff_spec := Nat.ldiff_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.lor_spec instead.")]
Notation lor_spec := Nat.lor_spec (only parsing).
#[deprecated(since="8.16",note="The NPeano file is obsolete. Use Nat.lxor_spec instead.")]
Notation lxor_spec := Nat.lxor_spec (only parsing).

Infix "<=?" := Nat.leb (at level 70) : nat_scope.
Infix "<?" := Nat.ltb (at level 70) : nat_scope.
Infix "^" := Nat.pow : nat_scope.
Infix "/" := Nat.div : nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.
Notation "( x | y )" := (Nat.divide x y) (at level 0) : nat_scope.

Require Import Even.
