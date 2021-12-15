Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 12178 lines to 457 lines, then from 500 lines to 147 lines, then from 175 lines to 56 lines *)
(* coqc version trunk (September 2014) compiled on Sep 21 2014 16:34:4 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (eaf864354c3fda9ddc1f03f0b1c7807b6fd44322) *)

Axiom transport : forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x), P y.
Axiom ap : forall {A B:Type} (f:A -> B) {x y:A} (p:x = y), f x = f y.
Module NonPrim.
  Class Contr_internal (A : Type) := { center : A ; contr : (forall y : A, center = y) }.
  Arguments center A {_} / .
  Inductive trunc_index : Type := minus_two | trunc_S (_ : trunc_index).
  Notation "-2" := minus_two (at level 0).
  Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
    match n with
      | -2 => Contr_internal A
      | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
    end.
  Class IsTrunc (n : trunc_index) (A : Type) : Type := Trunc_is_trunc : IsTrunc_internal n A.
  Notation Contr := (IsTrunc -2).
  Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.
  Goal forall (H : Type) (H0 : H -> H -> Type) (H1 : Type)
              (H2 : Contr H1) (H3 : H1) (H4 : H1 -> H)
              (H5 : H0 (H4 (center H1)) (H4 H3))
              (H6 : H0 (H4 (center H1)) (H4 (center H1))),
         transport (fun y : H => H0 (H4 (center H1)) y) (ap H4 (contr H3)) H6 = H5.
    intros.
    match goal with
      | [ |- context[contr (center _)] ] => fail 1 "bad"
      | _ => idtac
    end.
    match goal with
      | [ H : _ |- _ ] => destruct (contr H)
    end.
    match goal with
      | [ |- context[contr (center ?x)] ] => fail 1 "bad" x
      | _ => idtac
    end.
    admit.
  Defined.
End NonPrim.

Module Prim.
  Set Primitive Projections.
  Class Contr_internal (A : Type) := { center : A ; contr : (forall y : A, center = y) }.
  Arguments center A {_} / .
  Inductive trunc_index : Type := minus_two | trunc_S (_ : trunc_index).
  Notation "-2" := minus_two (at level 0).
  Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
    match n with
      | -2 => Contr_internal A
      | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
    end.
  Class IsTrunc (n : trunc_index) (A : Type) : Type := Trunc_is_trunc : IsTrunc_internal n A.
  Notation Contr := (IsTrunc -2).
  Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.
  Goal forall (H : Type) (H0 : H -> H -> Type) (H1 : Type)
              (H2 : Contr H1) (H3 : H1) (H4 : H1 -> H)
              (H5 : H0 (H4 (center H1)) (H4 H3))
              (H6 : H0 (H4 (center H1)) (H4 (center H1))),
         transport (fun y : H => H0 (H4 (center H1)) y) (ap H4 (contr H3)) H6 = H5.
    intros.
    match goal with
      | [ |- context[contr (center _)] ] => fail 1 "bad"
      | _ => idtac
    end.
    match goal with
      | [ H : _ |- _ ] => destruct (contr H)
    end.
    match goal with
      | [ |- context[contr (center ?x)] ] => fail 1 "bad" x
      | _ => idtac
    end. (* Error: Tactic failure: bad H1. *)
    admit.
  Defined.
End Prim.
