
Set Implicit Arguments.

Require Import Logic.
Module NonPrim.
Local Set Nonrecursive Elimination Schemes.
Record prodwithlet (A B : Type) : Type :=
  pair' { fst : A; fst' := fst; snd : B }.

Definition letreclet (p : prodwithlet nat nat) :=
  let (x, x', y) := p in x + y.

Definition pletreclet (p : prodwithlet nat nat) :=
  let 'pair' x x' y := p in x + y + x'.

Definition pletreclet2 (p : prodwithlet nat nat) :=
  let 'pair' x y := p in x + y.

Check (pair 0 0).
End NonPrim.

Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Local Set Nonrecursive Elimination Schemes.
Local Set Primitive Projections.

Record prod (A B : Type) : Type :=
  pair { fst : A; snd : B }.

Print prod_rect.

(* What I really want: *)
Definition prod_rect' A B (P : prod A B -> Type) (u : forall (fst : A) (snd : B), P (pair fst snd))
           (p : prod A B) : P p
  := u (fst p) (snd p).

Definition conv : @prod_rect = @prod_rect'.
Proof. reflexivity. Defined.

Definition imposs :=
  (fun A B P f (p : prod A B) => match p as p0 return P p0 with
                                   | {| fst := x ; snd := x0 |} => f x x0
                                 end).

Definition letrec (p : prod nat nat) :=
  let (x, y) := p in x + y.
Eval compute in letrec (pair 1 5).

Goal forall p : prod nat nat, letrec p = fst p + snd p.
Proof.
  reflexivity.
  Undo.
  intros p.
  case p. simpl. unfold letrec. simpl. reflexivity.
Defined.

Eval compute in conv. (* = eq_refl
     : prod_rect = prod_rect' *)

Check eq_refl : @prod_rect = @prod_rect'. (* Toplevel input, characters 6-13:
Error:
The term "eq_refl" has type "prod_rect = prod_rect"
while it is expected to have type "prod_rect = prod_rect'"
(cannot unify "prod_rect" and "prod_rect'"). *)

Record sigma (A : Type) (B : A -> Type) : Type :=
  dpair { pi1 : A ; pi2 : B pi1 }.



