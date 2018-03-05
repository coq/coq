(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

Require Export Relations_1.

Section Relations_2.
Variable U : Type.
Variable R : Relation U.

Inductive Rstar (x:U) : U -> Prop :=
  | Rstar_0 : Rstar x x
  | Rstar_n : forall y z:U, R x y -> Rstar y z -> Rstar x z.

Inductive Rstar1 (x:U) : U -> Prop :=
  | Rstar1_0 : Rstar1 x x
  | Rstar1_1 : forall y:U, R x y -> Rstar1 x y
  | Rstar1_n : forall y z:U, Rstar1 x y -> Rstar1 y z -> Rstar1 x z.

Inductive Rplus (x:U) : U -> Prop :=
  | Rplus_0 : forall y:U, R x y -> Rplus x y
  | Rplus_n : forall y z:U, R x y -> Rplus y z -> Rplus x z.

Definition Strongly_confluent : Prop :=
  forall x a b:U, R x a -> R x b -> ex (fun z:U => R a z /\ R b z).

End Relations_2.

Hint Resolve Rstar_0: sets.
Hint Resolve Rstar1_0: sets.
Hint Resolve Rstar1_1: sets.
Hint Resolve Rplus_0: sets.
