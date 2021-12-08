Unset Strict Universe Declaration.
Require Import TestSuite.admit.
(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
(* File reduced by coq-bug-finder from 5012 lines to 4659 lines, then from 4220 lines to 501 lines, then from 513 lines to 495 lines, then from 513 lines to 495 lines, then from 412 lines to 79 lines, then from 412 lines to 79 lines. *)
Set Universe Polymorphism.
Definition admit {T} : T.
Admitted.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Delimit Scope path_scope with path.
Local Open Scope path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
    match p with idpath => idpath end.

Class IsEquiv {A B : Type} (f : A -> B) :=
  BuildIsEquiv {
      equiv_inv : B -> A
    }.

Record Equiv A B :=
  BuildEquiv {
      equiv_fun :> A -> B ;
      equiv_isequiv :> IsEquiv equiv_fun
    }.

Existing Instance equiv_isequiv.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

Inductive Bool : Type := true | false.

Local Open Scope equiv_scope.
Definition equiv_path (A B : Type) (p : A = B) : A <~> B
  := BuildEquiv _ _ (transport (fun X:Type => X) p) admit.

Class Univalence :=
  isequiv_equiv_path :> forall (A B : Type), IsEquiv (equiv_path A B) .

Section Univalence.
  Context `{Univalence}.
  Definition path_universe_uncurried {A B : Type} (f : A <~> B) : A = B
    := (equiv_path A B)^-1 f.

  Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B)
    := path_universe_uncurried (BuildEquiv _ _ f feq).
End Univalence.

Definition e : Equiv@{i j} Bool Bool.
  admit.
Defined.

Definition p `{Univalence} : @paths Type Bool Bool := path_universe e.

Theorem thm `{Univalence} : (forall A, ((A -> False) -> False) -> A) -> False.
  intro f.
  Set Printing Universes.
  Set Printing All.
  Show Universes.
  pose proof (apD f p).
  pose proof (apD f (path_universe e)).
  admit.
Defined.  (* ??? Toplevel input, characters 0-37:
Error:
Unable to satisfy the following constraints:
In environment:
H : Univalence@{Top.144 Top.145 Top.146 Top.147 Top.148}
f : forall (A : Type{Top.150}) (_ : forall _ : forall _ : A, False, False), A

?57 : "@IsEquiv@{Top.150 Top.145} Bool Bool (equiv_fun@{Set Set} Bool Bool e)" *)
(* Toplevel input, characters 18-19:
Error:
In environment
H : Univalence (* Top.148 Top.149 Top.150 Top.151 *)
f : forall (A : Type (* Top.153 *))
      (_ : forall _ : forall _ : A, False, False), A
X : @paths (* Top.155 *)
      ((fun A : Type (* Top.153 *) =>
        forall _ : forall _ : forall _ : A, False, False, A) Bool)
      (@transport (* Top.154 Top.155 *) Type (* Top.153 *)
         (fun A : Type (* Top.153 *) =>
          forall _ : forall _ : forall _ : A, False, False, A) Bool Bool
         (@path_universe (* Top.148 Top.150 Top.151 Top.159 Top.153 Top.154
            Top.149 Top.153 *) H Bool Bool
            (equiv_fun (* Top.153 Top.153 *) Bool Bool e (* Top.153 *))
            (equiv_isequiv (* Top.153 Top.153 *) Bool Bool e (* Top.153 *)))
         (f Bool)) (f Bool)
The term "@p (* Top.148 Top.172 Top.151 Top.150 Top.149 *) H" has type
 "@paths (* Top.171 *) Set Bool Bool" while it is expected to have type
 "@paths (* Top.169 *) Type (* Top.153 *) ?62 ?63"
(Universe inconsistency: Cannot enforce Set = Top.153)). *)
