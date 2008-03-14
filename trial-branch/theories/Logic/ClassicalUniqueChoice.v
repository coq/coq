(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file provides classical logic and unique choice; this is
    weaker than providing iota operator and classical logic as the
    definite descriptions provided by the axiom of unique choice can
    be used only in a propositional context (especially, they cannot
    be used to build functions outside the scope of a theorem proof) *)

(** Classical logic and unique choice, as shown in
    [ChicliPottierSimpson02], implies the double-negation of
    excluded-middle in [Set], hence it implies a strongly classical
    world. Especially it conflicts with the impredicativity of [Set].

    [ChicliPottierSimpson02] Laurent Chicli, Lo�c Pottier, Carlos
    Simpson, Mathematical Quotients and Quotient Types in Coq,
    Proceedings of TYPES 2002, Lecture Notes in Computer Science 2646,
    Springer Verlag.  *)

Require Export Classical.

Axiom
  dependent_unique_choice :
    forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
      (forall x : A, exists! y : B x, R x y) ->
      (exists f : (forall x:A, B x), forall x:A, R x (f x)).

(** Unique choice reifies functional relations into functions *)

Theorem unique_choice :
 forall (A B:Type) (R:A -> B -> Prop),
   (forall x:A,  exists! y : B, R x y) ->
   (exists f:A->B, forall x:A, R x (f x)).
Proof.
intros A B.
apply (dependent_unique_choice A (fun _ => B)).
Qed.

(** The following proof comes from [ChicliPottierSimpson02] *)

Require Import Setoid.

Theorem classic_set : ((forall P:Prop, {P} + {~ P}) -> False) -> False.
Proof.
intro HnotEM.
set (R := fun A b => A /\ true = b \/ ~ A /\ false = b).
assert (H :  exists f : Prop -> bool, (forall A:Prop, R A (f A))).
apply unique_choice.
intro A.
destruct (classic A) as [Ha| Hnota].
  exists true; split.
    left; split; [ assumption | reflexivity ].
    intros y [[_ Hy]| [Hna _]].
      assumption.
      contradiction.
  exists false; split.
    right; split; [ assumption | reflexivity ].
    intros y [[Ha _]| [_ Hy]].
      contradiction.
      assumption.
destruct H as [f Hf].
apply HnotEM.
intro P.
assert (HfP := Hf P).
(* Elimination from Hf to Set is not allowed but from f to Set yes ! *)
destruct (f P).
  left.
  destruct HfP as [[Ha _]| [_ Hfalse]].
    assumption.
    discriminate.
  right.
  destruct HfP as [[_ Hfalse]| [Hna _]].
    discriminate.
    assumption.
Qed.
 
