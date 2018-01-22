Definition MR {T M : Type} :=
fun (R : M -> M -> Prop) (m : T -> M) (x y : T) => R (m x) (m y).

Set Primitive Projections.

Record sigma {A : Type} {B : A -> Type} : Type := sigmaI
  { pr1 : A;  pr2 : B pr1 }.

Axiom F : forall {A : Type} {R : A -> A -> Prop},
  (forall x, (forall y, R y x -> unit) -> unit) -> forall (x : A), unit.

Definition foo (A : Type) (l : list A) :=
  let y := {| pr1 := A; pr2 := l |} in
  let bar := MR lt (fun p : sigma =>
                 (fix Ffix (x : list (pr1 p)) : nat :=
                    match x with
                    | nil => 0
                    | cons _ x1 => S (Ffix x1)
                    end) (pr2 p)) in
fun (_ : bar y y) =>
F (fun (r : sigma)
       (X : forall q : sigma, bar q r -> unit) => tt).

Definition fooT (A : Type) (l : list A) : Type :=
  ltac:(let ty := type of (foo A l) in exact ty).
Parameter P : forall A l, fooT A l -> Prop.

Goal forall A l, P A l (foo A l).
Proof.
  intros; unfold foo.
  Fail match goal with
    | [ |- context [False]] => idtac
  end.
Admitted.
