(* Dependent higher-order hole in "refine" (simplified version) *)

Set Implicit Arguments.

Inductive Nest t := Cons : Nest (prod t t) -> Nest t.

Definition cast A x y Heq P H := @eq_rect A x P H y Heq.

Definition replace a (y:Nest (prod a a)) : a = a -> Nest a.

(* This used to raise an anomaly Unknown Meta in 8.2 and 8.3beta.
   It raises a regular error in 8.3 and almost succeeds with the new
   proof engine: there are two solutions to a unification problem
   (P:=\a.Nest (prod a a) and P:=\_.Nest (prod a a)) and refine should either
   leave P as subgoal or choose itself one solution *)

  intros. Fail refine (Cons (cast H _ y)).
  Unset Solve Unification Constraints. (* Keep the unification constraint around *)
  refine (Cons (cast H _ y)).
  intros.
  refine (Nest (prod X X)). Qed.
