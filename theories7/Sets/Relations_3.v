(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

(*i $Id$ i*)

Require Export Relations_1.
Require Export Relations_2.

Section Relations_3.
   Variable U: Type.
   Variable R: (Relation U).
   
   Definition coherent : U -> U -> Prop :=
      [x,y: U]  (EXT z | (Rstar U R x z) /\ (Rstar U R y z)).
   
   Definition locally_confluent : U -> Prop :=
      [x: U] (y,z: U) (R x y) -> (R x z) -> (coherent y z).
   
   Definition Locally_confluent : Prop :=  (x: U) (locally_confluent x).
   
   Definition confluent : U -> Prop :=
      [x: U] (y,z: U) (Rstar U R x y) -> (Rstar U R x z) -> (coherent y z).
   
   Definition Confluent : Prop :=  (x: U) (confluent x).
   
   Inductive  noetherian : U -> Prop :=
         definition_of_noetherian:
           (x: U) ((y: U) (R x y) -> (noetherian y)) -> (noetherian x).
   
   Definition Noetherian : Prop :=  (x: U) (noetherian x).
   
End Relations_3.
Hints Unfold  coherent : sets v62.
Hints Unfold  locally_confluent : sets v62.
Hints Unfold  confluent : sets v62.
Hints Unfold  Confluent : sets v62.
Hints Resolve definition_of_noetherian : sets v62.
Hints Unfold  Noetherian : sets v62.


