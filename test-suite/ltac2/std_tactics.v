Require Import Ltac2.Ltac2.

Axiom f: nat -> nat.
Definition g := f.

Axiom Foo1: nat -> Prop.
Axiom Foo2: nat -> Prop.
Axiom Impl: forall n: nat, Foo1 (f n) -> Foo2 (f n).

Create HintDb foo discriminated.
#[export] Hint Constants Opaque : foo.
#[export] Hint Resolve Impl : foo.

Goal forall x, Foo1 (f x) -> Foo2 (g x).
Proof.
  auto with foo.
  #[export] Hint Transparent g : foo.
  auto with foo.
Qed.

Goal forall (x: nat), exists y, f x = g y.
Proof.
  intros.
  eexists.
  unify f g.
  lazy_match! goal with
  | [ |- ?a ?b = ?rhs ] => unify ($a $b) $rhs
  end.
Abort.
