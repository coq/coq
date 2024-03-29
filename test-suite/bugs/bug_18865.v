#[universes(polymorphic)]
Inductive sig@{s s' s''|u v| } {A:Type@{s|u}} (P:A -> Type@{s'|v}) : Type@{s''|max(u,v)} :=
    exist : forall x:A, P x -> sig P.

Notation "{ x : A & P }" := (sig (A:=A) (fun x => P)) (at level 0, x at level 99) : type_scope.

#[universes(polymorphic)]
Definition proj1_sig@{s s'|u v| } {A:Type@{s|u}} {P:A -> Type@{s'|v}} (e:sig@{_ _ s|_ _} P) :=
  match e with
  | exist _ a b => a
  end.

Notation "x .1" := (proj1_sig x) (at level 1, left associativity, format "x .1").

Definition projT1_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v) : u.1 = v.1
  := match p with eq_refl => eq_refl end.

Context {A} {P : A -> Type} {u : { a : A & P a }} (b : P u.1).

Set Definitional UIP.

Inductive SEq (A : Type) (a : A) : forall (B : Type), B -> SProp := Seq_refl : SEq A a A a.

Check
@eq_refl _
  ((fun (A : Type) (a : A) (B: Type) (b : B) (e : SEq A a B b) =>
  match e with Seq_refl _ _ => tt end) _ (P u.1) _ (P u.1)
  ((fun x : SEq _ (P u.1) _ (P u.1) => x) (Seq_refl _ _))).

Check @eq_refl _
  ((fun (A : Type) (a : A) (B: Type) (b : B) (e : SEq A a B b) =>
  match e with Seq_refl _ _ => tt end) _ (P u.1) _ (P u.1)
  ((fun x : SEq _ (P u.1) _ (P u.1) => x) (Seq_refl _ _)))
  : tt = tt.
