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

Axiom dependent_description :
  (A:Type;B:A->Type;R: (x:A)(B x)->Prop)
  ((x:A)(EX y:(B x)|(R x y)/\ ((y':(B x))(R x y') -> y=y')))
   -> (EX f:(x:A)(B x) | (x:A)(R x (f x))).

(** Principle of definite descriptions (aka axiom of unique choice) *)

Theorem description :
  (A:Type;B:Type;R: A->B->Prop)
  ((x:A)(EX y:B|(R x y)/\ ((y':B)(R x y') -> y=y')))
   -> (EX f:A->B | (x:A)(R x (f x))).
Proof.
Intros A B.
Apply (dependent_description A [_]B).
Qed.

(** The followig proof comes from [1] *)

Theorem classic_set : (((P:Prop){P}+{~P}) -> False) -> False.
Proof.
Intro HnotEM.
Pose R:=[A,b]A/\true=b \/ ~A/\false=b.
Assert H:(EX f:Prop->bool|(A:Prop)(R A (f A))).
Apply description.
Intro A.
NewDestruct (classic A) as [Ha|Hnota].
  Exists true; Split.
    Left; Split; [Assumption|Reflexivity].
    Intros y [[_ Hy]|[Hna _]].
      Assumption.
      Contradiction.
  Exists false; Split.
    Right; Split; [Assumption|Reflexivity].
    Intros y [[Ha _]|[_ Hy]].
      Contradiction.
      Assumption.
NewDestruct H as [f Hf].
Apply HnotEM.
Intro P.
Assert HfP := (Hf P).
(* Elimination from Hf to Set is not allowed but from f to Set yes ! *)
NewDestruct (f P).
  Left.
  NewDestruct HfP as [[Ha _]|[_ Hfalse]].
    Assumption.
    Discriminate.
  Right.
  NewDestruct HfP as [[_ Hfalse]|[Hna _]].
    Discriminate.
    Assumption.
Qed.
 
