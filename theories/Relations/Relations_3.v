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

Set Implicit Arguments.

Section Relations_3.
   Variable U : Type.
   Variable R : relation U.
   
   Definition coherent (x y:U) : Prop :=
      exists z : _, Rstar R x z /\ Rstar R y z.
   
   Definition locally_confluent (x:U) : Prop :=
     forall y z:U, R x y -> R x z -> coherent y z.
   
   Definition Locally_confluent : Prop := forall x:U, locally_confluent x.
   
   Definition confluent (x:U) : Prop :=
     forall y z:U, Rstar R x y -> Rstar R x z -> coherent y z.
   
   Definition Confluent : Prop := forall x:U, confluent x.
   
   Inductive noetherian (x: U) : Prop :=
       definition_of_noetherian :
         (forall y:U, R x y -> noetherian y) -> noetherian x.
   
   Definition Noetherian : Prop := forall x:U, noetherian x.
   
End Relations_3.
Hint Unfold coherent: sets v62.
Hint Unfold locally_confluent: sets v62.
Hint Unfold confluent: sets v62.
Hint Unfold Confluent: sets v62.
Hint Resolve definition_of_noetherian: sets v62.
Hint Unfold Noetherian: sets v62.
