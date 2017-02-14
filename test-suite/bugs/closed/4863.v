Require Import Classes.DecidableClass.

Inductive Foo : Set :=
| foo1 | foo2.

Lemma Decidable_sumbool : forall P, {P}+{~P} -> Decidable P.
Proof.
  intros P H.
  refine (Build_Decidable _ (if H then true else false) _).
  intuition congruence.
Qed.

Hint Extern 100 (Decidable (?A = ?B)) => abstract (abstract (abstract (apply Decidable_sumbool; decide equality))) : typeclass_instances.

Goal forall (a b : Foo), {a=b}+{a<>b}.
intros.
abstract (abstract (decide equality)). (*abstract works here*)
Qed.

Check ltac:(abstract (exact I)) : True.

Goal forall (a b : Foo), Decidable (a=b) * Decidable (a=b).
intros.
split. typeclasses eauto. 
typeclasses eauto. Qed.

Goal forall (a b : Foo), Decidable (a=b) * Decidable (a=b).
intros.
split.
refine _.
refine _.
Defined.
(*fails*)
