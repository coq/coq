(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export NZAxioms.

Set Implicit Arguments.

Module Type NAxiomsSig.
Include Type NZOrdAxiomsSig.
Local Open Scope NumScope.

Axiom pred_0 : P 0 == 0.

Parameter Inline recursion : forall A : Type, A -> (t -> A -> A) -> t -> A.
Implicit Arguments recursion [A].

Declare Instance recursion_wd (A : Type) (Aeq : relation A) :
 Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) (@recursion A).

Axiom recursion_0 :
  forall (A : Type) (a : A) (f : t -> A -> A), recursion a f 0 = a.

Axiom recursion_succ :
  forall (A : Type) (Aeq : relation A) (a : A) (f : t -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n, Aeq (recursion a f (S n)) (f n (recursion a f n)).

End NAxiomsSig.

