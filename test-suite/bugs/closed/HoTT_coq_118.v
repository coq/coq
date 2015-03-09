Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 5631 lines to 557 lines, then from 526 lines to 181 lines, then from 189 lines to 154 lines, then from 153 lines to 107 lines, then from 97 lines to 56 lines, then from 50 lines to 37 lines *)
Generalizable All Variables.
Set Universe Polymorphism.
Definition admit {T} : T.
Admitted.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y" := (@paths _ x y) : type_scope.
Class Contr_internal (A : Type) := BuildContr { center : A }.
Arguments center A {_}.
Instance contr_paths_contr `{Contr_internal A} (x y : A) : Contr_internal (x = y) := admit.
Inductive Unit : Set := tt.
Instance contr_unit : Contr_internal Unit | 0 := admit.
Record PreCategory := { morphism : Type }.
Class IsIsomorphism {C : PreCategory} (m : morphism C) := { left_inverse : m = m }.
Definition indiscrete_category : PreCategory := @Build_PreCategory Unit.
Goal forall (X : Type) (_ : forall x y : X, Contr_internal (@paths X x y)) (s : X),
       @IsIsomorphism indiscrete_category tt -> True.
Proof.
  intros X H s [p].
  simpl in *.
  assert (idpath = p).
  clear.
  assert (H : forall p : tt = tt, idpath = p) by (intro; exact (center _)).
  clear H.
  exact (center _).
  (* Toplevel input, characters 15-32:
Error:
Unable to satisfy the following constraints:
In environment:
p : tt = tt

?46 : "Contr_internal (idpath = p)"
 *)
