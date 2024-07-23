Set Universe Polymorphism.

Inductive unit' := tt'.

Inductive eq {A : Type} (x : A) : A -> Prop :=
  eq_refl : eq x x.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.

Lemma posttest : True.
Proof.
  destruct tt eqn:V.
  Check V : eq tt tt. (* check that we did use the non stdlib eq *)

  destruct tt' eqn:V'.
  exact I.
Qed.
(*
In environment
u := tt : unit
The term "eq_refl u" has type "eq u u" while it is expected to have type "eq tt u".

if we remove the first destruct:
Error: Illegal application:
The term "@eq_refl@{foo.18}" of type "forall (A : Type@{foo.18}) (x : A), @eq@{foo.18} A x x"
cannot be applied to the terms
 "unit'@{foo.16}" : "Type@{foo.16}"
 "u" : "unit'@{foo.16}"
The 1st term has type "Type@{foo.16}" which should be a subtype of "Type@{foo.18}".

(the difference is because unit : Set but unit'@{u} : Type@{u})
*)
