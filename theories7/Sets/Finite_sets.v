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

Require Ensembles.

Section Ensembles_finis.
Variable U: Type.

Inductive Finite : (Ensemble U) -> Prop :=
      Empty_is_finite: (Finite (Empty_set U))
   |  Union_is_finite:
      (A: (Ensemble U)) (Finite A) -> 
      (x: U) ~ (In U A x) -> (Finite (Add U A x)).

Inductive cardinal : (Ensemble U) -> nat -> Prop :=
      card_empty: (cardinal (Empty_set U) O)
   |  card_add:
       (A: (Ensemble U)) (n: nat) (cardinal A n) ->
        (x: U) ~ (In U A x) -> (cardinal (Add U A x) (S n)).

End Ensembles_finis.

Hints Resolve Empty_is_finite Union_is_finite : sets v62.
Hints Resolve card_empty card_add : sets v62.

Require Constructive_sets.

Section Ensembles_finis_facts.
Variable U: Type.

Lemma cardinal_invert :
 (X: (Ensemble U)) (p:nat)(cardinal U X p) -> Case p of
           X == (Empty_set U)
   [n:nat] (EXT A | (EXT x | 
           X == (Add U A x) /\ ~ (In U A x) /\ (cardinal U A n))) end.
Proof.
NewInduction 1; Simpl; Auto.
Exists A; Exists x; Auto.
Qed.

Lemma cardinal_elim :
 (X: (Ensemble U)) (p:nat)(cardinal U X p) -> Case p of
                              X == (Empty_set U)
                             [n:nat](Inhabited U X) end.
Proof.
Intros X p C; Elim C; Simpl; Trivial with sets.
Qed.

End Ensembles_finis_facts.
