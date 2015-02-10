(* Computing the type constraints to be satisfied when building the
   return clause of a match with a match *)

Set Implicit Arguments.
Set Asymmetric Patterns.
  
Variable A : Type.
Variable typ : A -> Type.

Inductive t : list A -> Type :=
| snil  : t nil
| scons : forall (x : A) (e : typ x) (lx : list A) (le : t  lx), t (x::lx).

Definition car (x:A) (lx : list A) (s: t (x::lx)) : typ x :=
  match s in t l'  with
  | snil => False
  | scons _ e _ _ => e
  end.
