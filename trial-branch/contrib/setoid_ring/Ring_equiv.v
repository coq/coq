Require Import Setoid_ring_theory.
Require Import LegacyRing_theory.
Require Import Ring_theory.

Set Implicit Arguments.

Section Old2New.

Variable A : Type.

Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp : A -> A.
Variable Aeq : A -> A -> bool.
Variable R : Ring_Theory Aplus Amult Aone Azero Aopp Aeq.

Let Aminus := fun x y => Aplus x (Aopp y).

Lemma ring_equiv1 :
  ring_theory Azero Aone Aplus Amult Aminus Aopp (eq (A:=A)).
Proof.
destruct R.
split;  eauto.
Qed.

End Old2New.

Section New2OldRing.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable Rth : ring_theory rO rI radd rmul rsub ropp (eq (A:=R)).

 Variable reqb : R -> R -> bool.
 Variable reqb_ok : forall x y, reqb x y = true -> x = y.

 Lemma ring_equiv2 :
   Ring_Theory radd  rmul rI rO ropp reqb.
Proof.
elim Rth; intros; constructor;  eauto.
intros.
apply reqb_ok.
destruct (reqb x y); trivial; intros.
elim H.
Qed.

 Definition default_eqb : R -> R -> bool := fun x y => false.
 Lemma default_eqb_ok : forall x y, default_eqb x y = true -> x = y.
Proof.
discriminate 1.
Qed.

End New2OldRing.

Section New2OldSemiRing.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul: R->R->R).
 Variable SRth : semi_ring_theory rO rI radd rmul (eq (A:=R)).

 Variable reqb : R -> R -> bool.
 Variable reqb_ok : forall x y, reqb x y = true -> x = y.

 Lemma sring_equiv2 :
   Semi_Ring_Theory radd rmul rI rO reqb.
Proof.
elim SRth; intros; constructor;  eauto.
intros.
apply reqb_ok.
destruct (reqb x y); trivial; intros.
elim H.
Qed.

End New2OldSemiRing.
