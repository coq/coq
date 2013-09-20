Require Import List.
Require Import Program.

Inductive Tree : Set :=
| Br : Tree -> Tree -> Tree
| No : nat -> Tree
.

(* given a tree, we want to know which lists can
   be used to navigate exactly to a node *)
Inductive Exact : Tree -> list bool -> Prop :=
| exDone  n    :              Exact (No n)   nil
| exLeft  l r p: Exact l p -> Exact (Br l r) (true::p)
| exRight l r p: Exact r p -> Exact (Br l r) (false::p)
.

Definition unreachable A : False -> A.
intros.
destruct H.
Defined.

Program Fixpoint fetch t p (x:Exact t p) {struct t} :=
   match t, p with
   | No p' , nil      => p'
   | No p' , _::_     => unreachable nat _
   | Br l r, nil      => unreachable nat _
   | Br l r, true::t  => fetch l t _
   | Br l r, false::t => fetch r t _
   end.

Next Obligation. inversion x. Qed.
Next Obligation. inversion x. Qed.
Next Obligation. inversion x; trivial. Qed.
Next Obligation. inversion x; trivial. Qed.

