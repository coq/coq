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
{ Seq_refl : (x:A) (Aeq x x);
  Seq_sym : (x,y:A) (Aeq x y) -> (Aeq y x);
  Seq_trans : (x,y,z:A) (Aeq x y) -> (Aeq y z) -> (Aeq x z)
}.

End Setoid.

Definition Prop_S : (Setoid_Theory Prop iff).
Split; [Exact iff_refl | Exact iff_sym | Exact iff_trans].
Qed.

Add Setoid Prop iff Prop_S.

Hint prop_set : setoid := Resolve (Seq_refl Prop iff Prop_S).
Hint prop_set : setoid := Resolve (Seq_sym Prop iff Prop_S).
Hint prop_set : setoid := Resolve (Seq_trans Prop iff Prop_S).

Add Morphism or : or_ext.
Intros.
Inversion H1.
Left.
Inversion H.
Apply (H3 H2).

Right.
Inversion H0.
Apply (H3 H2).
Qed.

Add Morphism and : and_ext.
Intros.
Inversion H1.
Split.
Inversion H.
Apply (H4 H2).

Inversion H0.
Apply (H4 H3).
Qed.

Add Morphism not : not_ext.
Red ; Intros.
Apply H0.
Inversion H.
Apply (H3 H1).
Qed.

Definition fleche [A,B:Prop] := A -> B.

Add Morphism fleche : fleche_ext.
Unfold fleche.
Intros.
Inversion H0.
Inversion H.
Apply (H3 (H1 (H6 H2))).
Qed.

