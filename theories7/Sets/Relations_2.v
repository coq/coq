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

Section Relations_2.
Variable U: Type.
Variable R: (Relation U).

Inductive Rstar : (Relation U) :=
     Rstar_0: (x: U) (Rstar x x)
   | Rstar_n: (x, y, z: U) (R x y) -> (Rstar y z) -> (Rstar x z).

Inductive Rstar1 : (Relation U) :=
     Rstar1_0: (x: U) (Rstar1 x x)
   | Rstar1_1: (x: U) (y: U) (R x y) -> (Rstar1 x y)
   | Rstar1_n: (x, y, z: U) (Rstar1 x y) -> (Rstar1 y z) -> (Rstar1 x z).

Inductive Rplus : (Relation U) :=
     Rplus_0: (x, y: U) (R x y) -> (Rplus x y)
   | Rplus_n: (x, y, z: U) (R x y) -> (Rplus y z) -> (Rplus x z).

Definition Strongly_confluent : Prop :=
   (x, a, b: U) (R x a) -> (R x b) -> (exT U [z: U] (R a z) /\ (R b z)).

End Relations_2.

Hints Resolve Rstar_0 : sets v62.
Hints Resolve Rstar1_0 : sets v62.
Hints Resolve Rstar1_1 : sets v62.
Hints Resolve Rplus_0 : sets v62.
