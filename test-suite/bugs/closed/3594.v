(* File reduced by coq-bug-finder from original input, then from 8752 lines to 735 lines, then from 735 lines to 310 lines, then from 228 lines to 105 lines, then from 98 lines to 41 lines *)
(* coqc version trunk (September 2014) compiled on Sep 6 2014 6:15:6 with OCaml 4.01.0
   coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (3ea6d6888105edd5139ae0a4d8f8ecdb586aff6c) *)
Notation idmap := (fun x => x).
Axiom path_forall : forall {A : Type} {P : A -> Type} (f g : forall x : A, P x), (forall x, f x = g x) -> f = g.
Local Set Primitive Projections.
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Bind Scope category_scope with PreCategory.
Set Implicit Arguments.
Delimit Scope functor_scope with functor.
Record Functor (C D : PreCategory) := {}.
Definition opposite (C : PreCategory) : PreCategory := @Build_PreCategory C (fun s d => morphism C d s).
Notation "C ^op" := (opposite C) (at level 3, format "C '^op'") : category_scope.
Definition oppositeF C D (F : Functor C D) : Functor C^op D^op := Build_Functor (C^op) (D^op).
Local Notation "F ^op" := (oppositeF F) (at level 3, format "F ^op") : functor_scope.
Axiom oppositeF_involutive : forall C D (F : Functor C D), ((F^op)^op)%functor = F.
Local Open Scope functor_scope.
Goal forall C D : PreCategory,
       (fun c : Functor C^op D^op => (c^op)^op) = idmap.
  intros.
  exact (path_forall (fun F : Functor C^op D^op => (F^op)^op) _ (@oppositeF_involutive _ _)).
  Undo.
  Unset Printing Notations.
  Set Debug Unification.
(*   Check (eq_refl : Build_PreCategory (opposite D).(object) *)
(*                  (fun s d : (opposite D).(object) =>  *)
(*                     (opposite D).(morphism) d s) =  *)
(*                    @Build_PreCategory D (fun s d => morphism D d s)). *)
(* opposite D). *)
  exact (path_forall (fun F => (F^op)^op) _ (@oppositeF_involutive _ _)). 
Qed.
 (* Toplevel input, characters 22-101:
Error:
In environment
C : PreCategory
D : PreCategory
The term
 "path_forall
    (fun F : Functor (opposite C) (opposite D) => oppositeF (oppositeF F))
    (fun F : Functor (opposite C) (opposite D) => F)
    (oppositeF_involutive (D:=opposite D))" has type
 "eq (fun F : Functor (opposite C) (opposite D) => oppositeF (oppositeF F))
    (fun F : Functor (opposite C) (opposite D) => F)"
while it is expected to have type
 "eq (fun c : Functor (opposite C) (opposite D) => oppositeF (oppositeF c))
    (fun x : Functor (opposite C) (opposite D) => x)"
(cannot unify "{|
               object := opposite D;
               morphism := fun s d : opposite D => morphism (opposite D) d s |}"
and "opposite D").
 *)
