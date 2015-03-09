Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from 4464 lines to 4137 lines, then from 3683 lines to 118 lines, then from 124 lines to 75 lines. *)
Set Universe Polymorphism.
Definition admit {T} : T.
Admitted.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : forall x, f x = g x
  := fun x => match h with idpath => idpath end.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : forall x, f (equiv_inv x) = x
}.

Arguments eisretr {A B} f {_} _.

Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.
Local Open Scope equiv_scope.

Instance isequiv_path {A B : Type} (p : A = B)
  : IsEquiv (transport (fun X:Type => X) p) | 0
  := admit.
Definition equiv_path (A B : Type) (p : A = B) : A <~> B
  := BuildEquiv _ _ (transport (fun X:Type => X) p) _.

Class Univalence := {
  isequiv_equiv_path :> forall (A B : Type), IsEquiv (equiv_path A B)
}.

Section Univalence.
  Context `{Univalence}.

  Definition path_universe_uncurried {A B : Type} (f : A <~> B) : A = B
    := (equiv_path A B)^-1 f.

  Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B)
    := path_universe_uncurried (BuildEquiv _ _ f feq).

  Set Printing Universes.
  Definition transport_path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : A)
  : transport (fun X:Type => X) (path_universe f) z = f z
    := apD10 (ap (equiv_fun A B) (eisretr (equiv_path A B) (BuildEquiv _ _ f feq))) z.
  (* Toplevel input, characters 0-231:
Error: Illegal application:
The term "isequiv_equiv_path (* Top.1003 Top.1003 Top.1001 Top.997 *)"
of type
 "Univalence (* Top.1003 Top.1003 Top.1001 Top.997 *) ->
  forall (A : Type (* Top.1003 *)) (B : Type (* Top.997 *)),
  IsEquiv (* Top.1003 Top.1001 *)
    (equiv_path (* Top.997 Top.1003 Top.1001 Top.1003 *) A B)"
cannot be applied to the terms
 "H" : "Univalence (* Top.934 Top.935 Top.936 Top.937 *)"
 "A" : "Type (* Top.996 *)"
 "B" : "Type (* Top.997 *)"
The 1st term has type "Univalence (* Top.934 Top.935 Top.936 Top.937 *)"
which should be coercible to
 "Univalence (* Top.1003 Top.1003 Top.1001 Top.997 *)".
 *)
