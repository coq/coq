(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$: i*)

Section Setoid.

Variable A : Type.
Variable Aeq : A -> A -> Prop.

Record Setoid_Theory : Prop := 
  {Seq_refl : forall x:A, Aeq x x;
   Seq_sym : forall x y:A, Aeq x y -> Aeq y x;
   Seq_trans : forall x y z:A, Aeq x y -> Aeq y z -> Aeq x z}.

End Setoid.

Definition Prop_S : Setoid_Theory Prop iff.
split; [ exact iff_refl | exact iff_sym | exact iff_trans ].
Qed.

Add Setoid Prop iff Prop_S.

Hint Resolve (Seq_refl Prop iff Prop_S): setoid.
Hint Resolve (Seq_sym Prop iff Prop_S): setoid.
Hint Resolve (Seq_trans Prop iff Prop_S): setoid.

Add Morphism or : or_ext.
intros.
inversion H1.
left.
inversion H.
apply (H3 H2).

right.
inversion H0.
apply (H3 H2).
Qed.

Add Morphism and : and_ext.
intros.
inversion H1.
split.
inversion H.
apply (H4 H2).

inversion H0.
apply (H4 H3).
Qed.

Add Morphism not : not_ext.
red in |- *; intros.
apply H0.
inversion H.
apply (H3 H1).
Qed.

Definition fleche (A B:Prop) := A -> B.

Add Morphism fleche : fleche_ext.
unfold fleche in |- *.
intros.
inversion H0.
inversion H.
apply (H3 (H1 (H6 H2))).
Qed.
