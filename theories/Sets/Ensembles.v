(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
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

Section Ensembles.
Variable U: Type.

Definition Ensemble :=  U -> Prop. 

Definition In : Ensemble -> U -> Prop :=  [A: Ensemble] [x: U] (A x).

Definition Included : Ensemble -> Ensemble -> Prop :=
   [B, C: Ensemble] (x: U) (In B x) -> (In C x).

Inductive Empty_set : Ensemble :=
   .

Inductive Full_set : Ensemble :=
     Full_intro: (x: U) (In Full_set x).

(* NB The following definition builds-in equality of elements in U as 
   Leibniz equality. \\
   This may have to be changed if we replace U by a Setoid on U with its own
   equality eqs, with  
     [In_singleton: (y: U)(eqs x y) -> (In (Singleton x) y)]. *)

Inductive Singleton [x:U] : Ensemble :=
      In_singleton: (In (Singleton x) x).

Inductive Union [B, C: Ensemble] : Ensemble :=
     Union_introl: (x: U) (In B x) -> (In (Union B C) x)
   | Union_intror: (x: U) (In C x) -> (In (Union B C) x).

Definition Add : Ensemble -> U -> Ensemble :=
   [B: Ensemble] [x: U] (Union B (Singleton x)).

Inductive Intersection [B, C:Ensemble] : Ensemble :=
      Intersection_intro:
        (x: U) (In B x) -> (In C x) -> (In (Intersection B C) x).

Inductive Couple [x,y:U] : Ensemble :=
     Couple_l: (In (Couple x y) x)
   | Couple_r: (In (Couple x y) y).

Inductive Triple[x, y, z:U] : Ensemble :=
    Triple_l: (In (Triple x y z) x)
  | Triple_m: (In (Triple x y z) y)
  | Triple_r: (In (Triple x y z) z).

Definition Complement : Ensemble -> Ensemble :=
   [A: Ensemble] [x: U] ~ (In A x).

Definition Setminus : Ensemble -> Ensemble -> Ensemble :=
   [B: Ensemble] [C: Ensemble] [x: U] (In B x) /\ ~ (In C x).

Definition Subtract : Ensemble -> U -> Ensemble :=
   [B: Ensemble] [x: U] (Setminus B (Singleton x)).

Inductive Disjoint [B, C:Ensemble] : Prop :=
      Disjoint_intro: ((x: U) ~ (In (Intersection B C) x)) -> (Disjoint B C).

Inductive Inhabited [B:Ensemble] : Prop :=
      Inhabited_intro: (x: U) (In B x) -> (Inhabited B).

Definition Strict_Included : Ensemble -> Ensemble -> Prop :=
   [B, C: Ensemble] (Included B C) /\ ~ B == C.

Definition Same_set : Ensemble -> Ensemble -> Prop :=
   [B, C: Ensemble] (Included B C) /\ (Included C B).

(*************************************)
(*******  Extensionality Axiom *******)
(*************************************)
Axiom Extensionality_Ensembles:
   (A,B: Ensemble) (Same_set A B) -> A == B.
Hints Resolve Extensionality_Ensembles.

End Ensembles.

Hints Unfold In Included Same_set Strict_Included Add Setminus Subtract : sets v62.

Hints Resolve Union_introl Union_intror Intersection_intro In_singleton Couple_l
	Couple_r Triple_l Triple_m Triple_r Disjoint_intro 
	Extensionality_Ensembles : sets v62.
