(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Properties of a binary relation [R] on type [A] *)

Section Rstar.

Variable A : Type.  
Variable R : A->A->Prop.  

(** Definition of the reflexive-transitive closure [R*] of [R] *)
(** Smallest reflexive [P] containing [R o P] *)

Definition Rstar  := [x,y:A](P:A->A->Prop)
   ((u:A)(P u u))->((u:A)(v:A)(w:A)(R u v)->(P v w)->(P u w)) -> (P x y).  

Theorem Rstar_reflexive:  (x:A)(Rstar x x).
 Proof [x:A][P:A->A->Prop]
       [h1:(u:A)(P u u)][h2:(u:A)(v:A)(w:A)(R u v)->(P v w)->(P u w)]
       (h1 x).  
  
Theorem Rstar_R: (x:A)(y:A)(z:A)(R x y)->(Rstar y z)->(Rstar x z).
 Proof [x:A][y:A][z:A][t1:(R x y)][t2:(Rstar y z)]
       [P:A->A->Prop]
       [h1:(u:A)(P u u)][h2:(u:A)(v:A)(w:A)(R u v)->(P v w)->(P u w)]
       (h2 x y z t1 (t2 P h1 h2)).  
  
(** We conclude with transitivity of [Rstar] : *)

Theorem  Rstar_transitive:  (x:A)(y:A)(z:A)(Rstar x y)->(Rstar y z)->(Rstar x z).
 Proof  [x:A][y:A][z:A][h:(Rstar x y)]
        (h ([u:A][v:A](Rstar v z)->(Rstar u z))
           ([u:A][t:(Rstar u z)]t)
           ([u:A][v:A][w:A][t1:(R u v)][t2:(Rstar w z)->(Rstar v z)]
            [t3:(Rstar w z)](Rstar_R u v z t1 (t2 t3)))).  

(** Another characterization of [R*] *)
(** Smallest reflexive [P] containing [R o R*] *)

Definition Rstar' := [x:A][y:A](P:A->A->Prop)
    ((P x x))->((u:A)(R x u)->(Rstar u y)->(P x y)) -> (P x y).  

Theorem Rstar'_reflexive: (x:A)(Rstar' x x).
 Proof  [x:A][P:A->A->Prop][h:(P x x)][h':(u:A)(R x u)->(Rstar u x)->(P x x)]h.
  
Theorem Rstar'_R: (x:A)(y:A)(z:A)(R x z)->(Rstar z y)->(Rstar' x y).
 Proof  [x:A][y:A][z:A][t1:(R x z)][t2:(Rstar z y)]
        [P:A->A->Prop][h1:(P x x)]
        [h2:(u:A)(R x u)->(Rstar u y)->(P x y)](h2 z t1 t2).  
  
(** Equivalence of the two definitions: *)

Theorem Rstar'_Rstar:  (x:A)(y:A)(Rstar' x y)->(Rstar x y).
 Proof  [x:A][y:A][h:(Rstar' x y)]
        (h Rstar (Rstar_reflexive x) ([u:A](Rstar_R x u y))).  
  
Theorem Rstar_Rstar':  (x:A)(y:A)(Rstar x y)->(Rstar' x y).
 Proof  [x:A][y:A][h:(Rstar x y)](h Rstar' ([u:A](Rstar'_reflexive u))
         ([u:A][v:A][w:A][h1:(R u v)][h2:(Rstar' v w)]
          (Rstar'_R u w v h1 (Rstar'_Rstar v w h2)))).  


(** Property of Commutativity of two relations *)

Definition commut := [A:Set][R1,R2:A->A->Prop]
                       (x,y:A)(R1 y x)->(z:A)(R2 z y)
                        ->(EX y':A |(R2 y' x) & (R1 z y')).


End Rstar.

