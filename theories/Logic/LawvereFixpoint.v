(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A proof of Lawvere's fixpoint theorem, namely that a retract from
    [A] to [A->B] implies that [B] has a fixpoint. This is the core of
    several theorems by diagonalization: Cantor's theorem, halting
    problem, incompleteness theorem, Curry's Y fixpoint, ... *)

Local Set Primitive Projections.

Set Warnings "-future-coercion-class-field".

Class IsRetract {A B} (f : A -> B) := {
    retract_inv : B -> A;
    risretr : forall x:B, f (retract_inv x) = x;
  }.
Record Retract A B := { retract_fun :> A -> B ; retract_isretract :> IsRetract retract_fun }.

Class IsFix {A} (Fix : (A -> A) -> A) := isfix : forall f : A -> A, Fix f = f (Fix f).
Class HasFix A := { Fix : (A -> A) -> A ; Fix_eq : IsFix Fix }.

#[global] Arguments retract_fun {A B} _.
#[global] Arguments retract_isretract {A B} _.

Section fixpoint.
  Context {A B} (ϕ : A -> (A -> B)) (ψ : (A -> B) -> A).

  Definition fixpt (f : B -> B) : B
    := let q := fun a => f (ϕ a a) in
       let p := ψ q in
       ϕ p p.
End fixpoint.

Section lawvere.
  Context A B (retract : Retract A (A -> B)).

  Instance fixpt_eq : IsFix (fixpt retract retract.(retract_inv))
    := fun f => f_equal (fun f => f _) (retract.(risretr) _).

  Instance has_fixpt : HasFix B
    := { Fix := _ ; Fix_eq := fixpt_eq }.
End lawvere.
