Fail Inductive list' (A:Set) : Set :=
| nil' : list' A
| cons' : A -> list' A -> list' (A*A).

(* Check printing of let-ins *)
Inductive foo (A : Type) (x : A) (y := x) := Foo.

Print foo.

(* Check where clause *)
Reserved Notation "x ** y" (at level 40, left associativity).
Inductive myprod A B :=
  mypair : A -> B -> A ** B
  where "A ** B" := (myprod A B) (only parsing).

Check unit ** bool.

(* "option is template" *)
About option.
Set Printing Universes.
About option.
(* "option is template on xxx" *)

Module DiffParams.
  Fail Inductive B: Type :=
  | F: A -> B with
    Inductive A: Type := mkA.

  Fail Inductive B := { x : nat } with
      Inductive A := { y : nat }.
End DiffParams.

(* print squash info
   (can't test impredicative set squashes in this file) *)

About or.

Inductive sunit : SProp := stt.

About sunit.

Set Universe Polymorphism.

Polymorphic Inductive sempty@{q| |} : Type@{q|Set} := .

About sempty.

Polymorphic Inductive ssig@{q1 q2 q3|a b|}
  (A:Type@{q1|a})
  (B:A -> Type@{q2|b})
  : Type@{q3|max(a,b)}
  := sexist (a:A) (b:B a).

About ssig.

Polymorphic Inductive BoxP@{q|a|} (A:Type@{q|a}) : Prop := boxP (_:A).

About BoxP.
