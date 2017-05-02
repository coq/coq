(* -*- coq-prog-args: ("-require" "Coq.Compat.Coq84" "-compat" "8.4") -*- *)
Require Import Coq.Lists.List Coq.Logic.JMeq Program.Equality.
Set Printing Universes.
Inductive Foo (I : Type -> Type) (A : Type) : Type :=
| foo (B : Type) : A -> I B -> Foo I A.
Definition Family := Type -> Type.
Definition FooToo : Family -> Family := Foo.
Definition optionize (I : Type -> Type) (A : Type) := option (I A).
Definition bar (I : Type -> Type) (A : Type) : A -> option (I A) -> Foo(optionize I) A := foo (optionize I) A A.
Record Rec (I : Type -> Type) := { rec : forall A : Type, A -> I A -> Foo I A }.
Definition barRec : Rec (optionize id) := {| rec := bar id |}.
Inductive Empty {T} : T -> Prop := .
Theorem empty (family : Family) (a : fold_right prod unit (map (Foo family)
nil)) (b : unit) :
  Empty (a, b) -> False.
Proof.
  intro e.
  dependent induction e.
Qed.
