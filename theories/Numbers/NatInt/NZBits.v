(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Bool NZAxioms NZMulOrder NZParity NZPow NZDiv NZLog.

(** Axiomatization of some bitwise operations *)

Module Type Bits (Import A : Typ).
 Parameter Inline testbit : t -> t -> bool.
 Parameters Inline shiftl shiftr land lor ldiff lxor : t -> t -> t.
 Parameter Inline div2 : t -> t.
End Bits.

Module Type BitsNotation (Import A : Typ)(Import B : Bits A).
 Notation "a .[ n ]" := (testbit a n) (at level 5, format "a .[ n ]").
 Infix ">>" := shiftr (at level 30, no associativity).
 Infix "<<" := shiftl (at level 30, no associativity).
End BitsNotation.

Module Type Bits' (A:Typ) := Bits A <+ BitsNotation A.

(** For specifying [testbit], we do not rely on division and modulo,
  since such a specification won't be easy to prove for particular
  implementations: advanced properties of / and mod won't be
  available at that moment. Instead, we decompose the number in
  low and high part, with the considered bit in the middle.

  Interestingly, this specification also holds for negative numbers,
  (with a positive low part and a negative high part), and this will
  correspond to a two's complement representation.

  Moreover, we arbitrary choose false as result of [testbit] at
  negative bit indexes (if they exist).
*)

Module Type NZBitsSpec
 (Import A : NZOrdAxiomsSig')(Import B : Pow' A)(Import C : Bits' A).

 Axiom testbit_spec : forall a n, 0<=n ->
  exists l, exists h, 0<=l<2^n /\
    a == l + ((if a.[n] then 1 else 0) + 2*h)*2^n.
 Axiom testbit_neg_r : forall a n, n<0 -> a.[n] = false.

 Axiom shiftr_spec : forall a n m, 0<=m -> (a >> n).[m] = a.[m+n].
 Axiom shiftl_spec_high : forall a n m, 0<=m -> n<=m -> (a << n).[m] = a.[m-n].
 Axiom shiftl_spec_low : forall a n m, m<n -> (a << n).[m] = false.

 Axiom land_spec : forall a b n, (land a b).[n] = a.[n] && b.[n].
 Axiom lor_spec : forall a b n, (lor a b).[n] = a.[n] || b.[n].
 Axiom ldiff_spec : forall a b n, (ldiff a b).[n] = a.[n] && negb b.[n].
 Axiom lxor_spec : forall a b n, (lxor a b).[n] = xorb a.[n] b.[n].
 Axiom div2_spec : forall a, div2 a == a >> 1.

End NZBitsSpec.

Module Type NZBits (A:NZOrdAxiomsSig)(B:Pow A) := Bits A <+ NZBitsSpec A B.
Module Type NZBits' (A:NZOrdAxiomsSig)(B:Pow A) := Bits' A <+ NZBitsSpec A B.

(** In the functor of properties will also be defined:
   - [setbit : t -> t -> t ] defined as [lor a (1<<n)].
   - [clearbit : t -> t -> t ] defined as [ldiff a (1<<n)].
   - [ones : t -> t], the number with [n] initial true bits,
     corresponding to [2^n - 1].
   - a logical complement [lnot]. For integer numbers it will
     be a [t->t], doing a swap of all bits, while on natural
     numbers, it will be a bounded complement [t->t->t], swapping
     only the first [n] bits.
*)

(** For the moment, no shared properties about NZ here,
  since properties and proofs for N and Z are quite different *)
