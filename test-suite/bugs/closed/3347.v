Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 12653 lines to 12453 lines, then from 11673 lines to 681 lines, then from 693 lines to 469 lines, then from 375 lines to 56 lines *)
Set Universe Polymorphism.
Notation Type1 := ltac:(let U := constr:(Type) in let gt := constr:(Set : U) in exact U) (only parsing).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Inductive Unit : Type1 := tt : Unit.
Fail Check Unit : Set. (* [Check Unit : Set] should fail if [Type1] is defined correctly *)
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Record Functor (C D : PreCategory) := { object_of :> C -> D }.
Definition indiscrete_category X : PreCategory := @Build_PreCategory X (fun _ _ => Unit).
Definition from_terminal (C : PreCategory) one (c : C) := Build_Functor one C (fun _ => c).
Local Notation "! x" := (from_terminal _ (indiscrete_category Unit) x) (at level 3).
Record NaturalTransformation {C D} (F G : Functor C D) :=
  { components_of :> forall c, morphism D (F c) (G c);
    commutes : forall c, components_of c = components_of c }.
Definition slice_category_induced_functor_nt (D : PreCategory) s d (m : morphism D s d)
: NaturalTransformation !s !d.
Proof.
  exists (fun _ : Unit => m);
  simpl; intros; clear;
  abstract admit.
Defined.
(* Toplevel input, characters 15-23:
Error: Illegal application:
The term "Build_NaturalTransformation" of type
 "forall (C D : PreCategory) (F G : Functor C D)
    (components_of : forall c : C, morphism D (F c) (G c)),
  (forall c : C, components_of c = components_of c) ->
  NaturalTransformation F G"
cannot be applied to the terms
 "indiscrete_category Unit" : "PreCategory"
 "D" : "PreCategory"
 "! s" : "Functor (indiscrete_category Unit) D"
 "! d" : "Functor (indiscrete_category Unit) D"
 "fun _ : Unit => m" : "Unit -> morphism D s d"
 "fun _ : Unit => slice_category_induced_functor_nt_subproof D s d m"
   : "forall c : indiscrete_category Unit, m = m"
The 5th term has type "Unit -> morphism D s d" which should be coercible to
 "forall c : indiscrete_category Unit, morphism D (! s c) (! d c)".
 *)
