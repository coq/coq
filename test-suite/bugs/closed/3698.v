Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 5479 lines to 4682 lines, then from 4214 lines to 86 lines, then from 60 lines to 25 lines *)
(* coqc version trunk (October 2014) compiled on Oct 1 2014 18:13:54 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (68846802a7be637ec805a5e374655a426b5723a5) *)
Set Primitive Projections.
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.
Notation pr1 := projT1.
Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Axiom ap : forall {A B:Type} (f:A -> B) {x y:A} (p:x = y), f x = f y.
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A }.
Record Equiv A B := { equiv_fun :> A -> B ; equiv_isequiv :> IsEquiv equiv_fun }.
Global Existing Instance equiv_isequiv.
Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : equiv_scope.
Axiom IsHSet : Type -> Type.
Local Open Scope equiv_scope.
Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
Axiom issig_hSet: (sigT IsHSet) <~> hSet.
Definition isequiv_ap_setT X Y : IsEquiv (@ap _ _ setT X Y).
Proof.
  assert (H'' : forall g : X = Y -> (issig_hSet^-1 X).1 = (issig_hSet^-1 Y).1,
                  g = g -> IsEquiv g) by admit.
  Eval compute in (@projT1 Type IsHSet (@equiv_inv _ _ _ (equiv_isequiv _ _ issig_hSet) X)).
  Fail apply H''. (* stack overflow *)
