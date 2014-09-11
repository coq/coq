(* File reduced by coq-bug-finder from original input, then from 7421 lines to 6082 lines, then from 5860 lines to 5369 lines, then from 5300 lines to 165 lines, then from 111 lines to 38 lines *)
Set Implicit Arguments.
Record PreCategory :=
  { object :> Type;
    morphism : object -> object -> Type;
    identity : forall x, morphism x x }.
Bind Scope category_scope with PreCategory.
Local Notation "1" := (identity _ _) : morphism_scope.
Local Open Scope morphism_scope.
Definition prod (C D : PreCategory) : PreCategory
  := @Build_PreCategory
       (C * D)%type
       (fun s d => (morphism C (fst s) (fst d) * morphism D (snd s) (snd d))%type)
       (fun x => (identity _ (fst x), identity _ (snd x))).
Local Infix "*" := prod : category_scope.
Module NonPrim.
  Record Functor (C D : PreCategory) :=
    { object_of :> C -> D;
      morphism_of : forall s d, morphism C s d -> morphism D (object_of s) (object_of d);
      identity_of : forall x, morphism_of _ _ (identity _ x) = identity _ (object_of x) }.
  Notation "F '_1' m" := (morphism_of F _ _ m) (at level 10, no associativity) : morphism_scope.
  Goal forall C1 C2 D (F : Functor (C1 * C2) D) x, F _1 (1, 1) = identity _ (F x).
  Proof.
    intros.
    rewrite identity_of.
    reflexivity.
  Qed.
End NonPrim.
Module Prim.
  Set Primitive Projections.
  Record Functor (C D : PreCategory) :=
    { object_of :> C -> D;
      morphism_of : forall s d, morphism C s d -> morphism D (object_of s) (object_of d);
      identity_of : forall x, morphism_of _ _ (identity _ x) = identity _ (object_of x) }.
  Notation "F '_1' m" := (morphism_of F _ _ m) (at level 10, no associativity) : morphism_scope.
  Goal forall C1 C2 D (F : Functor (C1 * C2) D) x, F _1 (1, 1) = identity _ (F x).
  Proof.
    intros.
    rewrite identity_of. (* Toplevel input, characters 0-20:
Error:
Found no subterm matching "morphism_of ?192 ?193 ?193 (identity ?190 ?193)" in the current goal. *)
    reflexivity.
  Qed.
End Prim.
