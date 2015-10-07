Unset Strict Universe Declaration.
Notation idmap := (fun x => x).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Delimit Scope path_scope with path.
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z := match p, q with idpath, idpath => idpath end.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x := match p with idpath => idpath end.
Notation "p @ q" := (concat p q) (at level 20) : path_scope.
Notation "p ^" := (inverse p) (at level 3, format "p '^'") : path_scope.
Class IsEquiv {A B : Type} (f : A -> B) := {}.
Axiom path_universe : forall {A B : Type} (f : A -> B) {feq : IsEquiv f}, (A = B).

Definition Lift : Type@{i} -> Type@{j}
  := Eval hnf in let lt := Type@{i} : Type@{j} in fun T => T.

Definition lift {T} : T -> Lift T := fun x => x.

Goal forall x y : Type, x = y.
  intros.
  pose proof ((fun H0 : idmap _ => (@path_universe _ _ (@lift x) (H0 x) @ 
                                                   (@path_universe _ _ (@lift x) (H0 x))^)))%path as H''.
