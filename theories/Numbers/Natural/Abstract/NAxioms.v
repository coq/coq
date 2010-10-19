(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export NZAxioms NZPow NZSqrt NZDiv.

(** From [NZ], we obtain natural numbers just by stating that [pred 0] == 0 *)

Module Type NAxiom (Import NZ : NZDomainSig').
 Axiom pred_0 : P 0 == 0.
End NAxiom.

Module Type NAxiomsMiniSig := NZOrdAxiomsSig <+ NAxiom.
Module Type NAxiomsMiniSig' := NZOrdAxiomsSig' <+ NAxiom.


(** Let's now add some more functions and their specification *)

(** Parity functions *)

Module Type Parity (Import N : NAxiomsMiniSig').
 Parameter Inline even odd : t -> bool.
 Definition Even n := exists m, n == 2*m.
 Definition Odd n := exists m, n == 2*m+1.
 Axiom even_spec : forall n, even n = true <-> Even n.
 Axiom odd_spec : forall n, odd n = true <-> Odd n.
End Parity.

(** For Power and Sqrt functions : NZPow and NZSqrt are enough *)

(** Division Function : we reuse NZDiv.DivMod and NZDiv.NZDivCommon,
    and add to that a N-specific constraint. *)

Module Type NDivSpecific (Import N : NAxiomsMiniSig')(Import DM : DivMod' N).
 Axiom mod_upper_bound : forall a b, b ~= 0 -> a mod b < b.
End NDivSpecific.


(** We now group everything together. *)

Module Type NAxiomsSig := NAxiomsMiniSig <+ HasCompare <+ Parity
  <+ NZPow.NZPow <+ NZSqrt.NZSqrt
  <+ DivMod <+ NZDivCommon <+ NDivSpecific.

Module Type NAxiomsSig' := NAxiomsMiniSig' <+ HasCompare <+ Parity
  <+ NZPow.NZPow' <+ NZSqrt.NZSqrt'
  <+ DivMod' <+ NZDivCommon <+ NDivSpecific.


(** It could also be interesting to have a constructive recursor function. *)

Module Type NAxiomsRec (Import NZ : NZDomainSig').

Parameter Inline recursion : forall {A : Type}, A -> (t -> A -> A) -> t -> A.

Declare Instance recursion_wd {A : Type} (Aeq : relation A) :
 Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) recursion.

Axiom recursion_0 :
  forall {A} (a : A) (f : t -> A -> A), recursion a f 0 = a.

Axiom recursion_succ :
  forall {A} (Aeq : relation A) (a : A) (f : t -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n, Aeq (recursion a f (S n)) (f n (recursion a f n)).

End NAxiomsRec.

Module Type NAxiomsFullSig := NAxiomsSig <+ NAxiomsRec.
Module Type NAxiomsFullSig' := NAxiomsSig' <+ NAxiomsRec.
