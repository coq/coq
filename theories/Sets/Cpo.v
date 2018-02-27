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

Require Export Ensembles.
Require Export Relations_1.
Require Export Partial_Order.

Section Bounds.
  Variable U : Type.
  Variable D : PO U.

  Let C := @Carrier_of U D.

  Let R := @Rel_of U D.

  Inductive Upper_Bound (B:Ensemble U) (x:U) : Prop :=
    Upper_Bound_definition :
    In U C x -> (forall y:U, In U B y -> R y x) -> Upper_Bound B x.

  Inductive Lower_Bound (B:Ensemble U) (x:U) : Prop :=
    Lower_Bound_definition :
    In U C x -> (forall y:U, In U B y -> R x y) -> Lower_Bound B x.

  Inductive Lub (B:Ensemble U) (x:U) : Prop :=
    Lub_definition :
    Upper_Bound B x -> (forall y:U, Upper_Bound B y -> R x y) -> Lub B x.

  Inductive Glb (B:Ensemble U) (x:U) : Prop :=
    Glb_definition :
    Lower_Bound B x -> (forall y:U, Lower_Bound B y -> R y x) -> Glb B x.

  Inductive Bottom (bot:U) : Prop :=
    Bottom_definition :
    In U C bot -> (forall y:U, In U C y -> R bot y) -> Bottom bot.

  Inductive Totally_ordered (B:Ensemble U) : Prop :=
    Totally_ordered_definition :
    (Included U B C ->
      forall x y:U, Included U (Couple U x y) B -> R x y \/ R y x) ->
    Totally_ordered B.

  Definition Compatible : Relation U :=
    fun x y:U =>
      In U C x ->
      In U C y ->  exists z : _, In U C z /\ Upper_Bound (Couple U x y) z.

  Inductive Directed (X:Ensemble U) : Prop :=
    Definition_of_Directed :
    Included U X C ->
    Inhabited U X ->
    (forall x1 x2:U,
      Included U (Couple U x1 x2) X ->
      exists x3 : _, In U X x3 /\ Upper_Bound (Couple U x1 x2) x3) ->
    Directed X.

  Inductive Complete : Prop :=
    Definition_of_Complete :
    (exists bot : _, Bottom bot) ->
    (forall X:Ensemble U, Directed X ->  exists bsup : _, Lub X bsup) ->
    Complete.

  Inductive Conditionally_complete : Prop :=
    Definition_of_Conditionally_complete :
    (forall X:Ensemble U,
      Included U X C ->
      (exists maj : _, Upper_Bound X maj) ->
      exists bsup : _, Lub X bsup) -> Conditionally_complete.
End Bounds.

Hint Resolve Totally_ordered_definition Upper_Bound_definition
  Lower_Bound_definition Lub_definition Glb_definition Bottom_definition
  Definition_of_Complete Definition_of_Complete
  Definition_of_Conditionally_complete.

Section Specific_orders.
  Variable U : Type.

  Record Cpo : Type := Definition_of_cpo
    {PO_of_cpo : PO U; Cpo_cond : Complete U PO_of_cpo}.

  Record Chain : Type := Definition_of_chain
    {PO_of_chain : PO U;
    Chain_cond : Totally_ordered U PO_of_chain (@Carrier_of _ PO_of_chain)}.

End Specific_orders.
