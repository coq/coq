Require Import TestSuite.admit.
Require Coq.Lists.List.
Require Coq.Sets.Ensembles.
Import Coq.Sets.Ensembles.
Global Set Implicit Arguments.
Delimit Scope comp_scope with comp.
Inductive Comp : Type -> Type :=
| Return : forall A, A -> Comp A
| Bind : forall A B, Comp A -> (A -> Comp B) -> Comp B
| Pick : forall A, Ensemble A -> Comp A.
Notation ret := Return.
Notation "x <- y ; z" := (Bind y%comp (fun x => z%comp))
                           (at level 81, right associativity,
                            format "'[v' x  <-  y ; '/' z ']'") : comp_scope.
Axiom refine : forall {A} (old : Comp A) (new : Comp A), Prop.
Open Scope comp.
Axiom elements : forall {A} (ls : list A), Ensemble A.
Axiom to_list : forall {A} (S : Ensemble A), Comp (list A).
Axiom finite_set_handle_cardinal : refine (ret 0) (ret 0).
Definition sumUniqueSpec (ls : list nat) : Comp nat.
  exact (ls' <- to_list (elements ls);
         List.fold_right (fun a b' => Bind b' ((fun a b => ret (a + b)) a)) (ret 0) ls').
Defined.
Axiom admit : forall {T}, T.
Definition sumUniqueImpl (ls : list nat)
: { c : _ | refine (sumUniqueSpec ls) (ret c) }%type.
Proof.
  eexists.
  match goal with
    | [ |- refine ?a ?b ] => let a' := eval hnf in a in change (refine a' b)
  end.
  try setoid_rewrite (@finite_set_handle_cardinal).
Abort.
