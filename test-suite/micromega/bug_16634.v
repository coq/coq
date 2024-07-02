From Coq Require Import List Psatz.

Set Psatz Conversion.

Lemma foo {A : Type} (xs : list A) : @length (id A) xs = @length A xs.
Proof.
  lia.
Qed.

Structure my_struct := {
  the_type : Type
}.

Coercion the_type : my_struct >-> Sortclass.

Arguments the_type : simpl never.

Definition A : Type := nat.
Definition A_struct := Build_my_struct A.

Lemma foo2 (xs ys zs : list A_struct) :
  @length (the_type A_struct) xs <= @length A ys ->
  @length (the_type A_struct) ys <= @length A zs ->
  @length A xs <= @length (the_type A_struct) zs.
Proof.
  intros.
  lia.
Qed.
