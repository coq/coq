Require Import ssreflect.

Generalizable Variables A B.

Class Inhab (A:Type) : Type :=
  { arbitrary : A }.

Lemma test_intro_typeclass_1 : forall A `{Inhab A} (x:A), x = arbitrary -> x = arbitrary.
Proof.
move =>> H. (* introduces [H:x=arbitrary] because first non dependent hypothesis *)
Abort.

Lemma test_intro_typeclass_2 : forall A `{Inhab A} (l1 l2:list A), l2 = nil -> app l1 l2 = l1.
Proof.
move =>> H. (* introduces [Inhab A] automatically because it is a typeclass instance *)
Abort.

Lemma test_intro_typeclass_3 : forall `{Inhab A, Inhab B} (x:A) (y:B), True -> x = x.
Proof. (* Above types [A] and [B] are implicitly quantified *)
move =>> y H. (* introduces the two typeclass instances automatically *)
Abort.

Class Foo `{Inhab A} : Type :=
  { foo : A }.

Lemma test_intro_typeclass_4 : forall `{Foo A}, True -> True.
Proof. (* Above, [A] and [{Inhab A}] are implicitly quantified *)
move =>> H. (* introduces [A] and [Inhab A] because they are dependently used,
               and introduce [Foo A] automatically because it is an instance. *)
Abort.
