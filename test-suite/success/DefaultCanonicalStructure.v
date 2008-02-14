
(* An example with default canonical structures *)

Variable A B : Type.
Variable plusA : A -> A -> A.
Variable plusB : B -> B -> B.
Variable zeroA : A.
Variable zeroB : B.
Variable eqA : A -> A -> Prop.
Variable eqB : B -> B -> Prop.
Variable phi : A -> B.

Set Implicit Arguments.

Record img := {
  ia : A;
  ib :> B;
  prf : phi ia = ib
}.

Parameter eq_img : forall (i1:img) (i2:img),
  eqB (ib i1) (ib i2) -> eqA (ia i1) (ia i2).

Lemma phi_img (a:A) : img.
  intro a.
  exists  a (phi a).
  refine ( refl_equal _).
Defined.
Canonical Structure phi_img.

Lemma zero_img : img.
  exists zeroA zeroB.
  admit.
Defined.
Canonical Structure zero_img.

Lemma plus_img : img -> img -> img.
intros i1 i2.
exists (plusA (ia i1) (ia i2)) (plusB (ib i1) (ib i2)).
admit.
Defined.
Canonical Structure plus_img.

Print Canonical Projections.

Goal forall a1 a2, eqA (plusA a1 zeroA) a2.
  intros a1 a2.
  refine  (eq_img _ _  _); simpl.
Admitted.
