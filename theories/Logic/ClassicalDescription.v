(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file provides classical logic and definite description *)

(** Classical logic and definite description, as shown in [1],
    implies the double-negation of excluded-middle in Set, hence it
    implies a strongly classical world. Especially it conflicts with
    impredicativity of Set, knowing that true<>false in Set.

    [1] Laurent Chicli, Loïc Pottier, Carlos Simpson, Mathematical
    Quotients and Quotient Types in Coq, Proceedings of TYPES 2002,
    Lecture Notes in Computer Science 2646, Springer Verlag.
*)

Require Export Classical.

Axiom
  dependent_description :
    forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
      (forall x:A,
          exists y : B x, R x y /\ (forall y':B x, R x y' -> y = y')) ->
       exists f : forall x:A, B x, (forall x:A, R x (f x)).

(** Principle of definite descriptions (aka axiom of unique choice) *)

Theorem description :
 forall (A B:Type) (R:A -> B -> Prop),
   (forall x:A,  exists y : B, R x y /\ (forall y':B, R x y' -> y = y')) ->
    exists f : A -> B, (forall x:A, R x (f x)).
Proof.
intros A B.
apply (dependent_description A (fun _ => B)).
Qed.

(** The followig proof comes from [1] *)

Theorem classic_set : ((forall P:Prop, {P} + {~ P}) -> False) -> False.
Proof.
intro HnotEM.
set (R := fun A b => A /\ true = b \/ ~ A /\ false = b).
assert (H :  exists f : Prop -> bool, (forall A:Prop, R A (f A))).
apply description.
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
 
