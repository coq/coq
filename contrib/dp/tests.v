
Require Import ZArith.
Require Import Classical.

(* First example with the 0 and the equality translated *)

Goal 0 = 0.
zenon.
Qed.


(* Examples in the Propositional Calculus
   and theory of equality *)

Parameter A C : Prop.

Goal A -> A.
zenon.
Qed.


Goal A -> (A \/ C).

zenon.
Qed.


Parameter x y z : Z.

Goal x = y -> y = z -> x = z.

zenon.
Qed.


Goal ((((A -> C) -> A) -> A) -> C) -> C.

zenon.
Qed.


(* Arithmetic *)
Open Scope Z_scope.

Goal 1 + 1 = 2.
simplify.
Qed.


Goal 2*x + 10 = 18 -> x = 4.

simplify.
Qed.


(* Universal quantifier *)

Goal (forall (x y : Z), x = y) -> 0=1.
try zenon.
simplify.
Qed.

Goal forall (x: nat), (x + 0 = x)%nat.

induction x0.
zenon.
zenon.
Qed.


(* No decision procedure can solve this problem 
  Goal forall (x a b : Z), a * x + b = 0 -> x = - b/a.
*)


(* Functions definitions *) 

Definition fst (x y : Z) : Z := x.

Goal forall (g : Z -> Z) (x y : Z), g (fst x y) = g x.

simplify.
Qed.


(* Eta-expansion example *)

Definition snd_of_3 (x y z : Z) : Z := y.

Definition f : Z -> Z -> Z := snd_of_3 0.

Goal forall (x y z z1 : Z), snd_of_3 x y z = f y z1.

simplify.
Qed.


(* Inductive types definitions - call to incontrib/dp/jection function *)

Inductive even : Z -> Prop :=
| even_0 : even 0
| even_plus2 : forall z : Z, even z -> even (z + 2).


(* Simplify and Zenon can't prove this goal before the timeout
   unlike CVC Lite *)

Goal even 4.
cvcl.
Qed.


Definition skip_z (z : Z) (n : nat) := n.

Definition skip_z1 := skip_z.

Goal forall (z : Z) (n : nat), skip_z z n = skip_z1 z n.

zenon.
Qed.


(* Axioms definitions and dp_hint *)

Parameter add : nat -> nat -> nat.
Axiom add_0 : forall (n : nat), add 0%nat n = n.
Axiom add_S : forall (n1 n2 : nat), add (S n1) n2 = S (add n1 n2).

Dp_hint add_0.
Dp_hint add_S.

(* Simplify can't prove this goal before the timeout 
   unlike zenon *)

Goal forall n : nat, add n 0 = n.

induction n ; zenon.
Qed.


Definition pred (n : nat) : nat := match n with
  | 0%nat => 0%nat
  | S n' => n'
end.

Goal forall n : nat, n <> 0%nat -> pred (S n) <> 0%nat.

zenon.
Qed.


Fixpoint plus (n m : nat) {struct n} : nat :=
  match n with
  | 0%nat => m
  | S n' => S (plus n' m)
end.

Goal forall n : nat, plus n 0%nat = n.

induction n; zenon.
Qed.


(* Mutually recursive functions *)

Fixpoint even_b (n : nat) : bool := match n with
  | O => true
  | S m => odd_b m
end
with odd_b (n : nat) : bool := match n with
  | O => false
  | S m => even_b m
end.

Goal even_b (S (S O)) = true.

zenon.
Qed.


(* sorts issues *)

Parameter foo : Set.         
Parameter ff : nat -> foo -> foo -> nat.
Parameter g : foo -> foo.
Goal (forall x:foo, ff 0 x x = O) -> forall y, ff 0 (g y) (g y) = O.
zenon.
Qed.



(* abstractions *)

Parameter poly_f : forall A:Set, A->A.

Goal forall x:nat, poly_f nat x = poly_f nat x.
zenon.
Qed.



(* Anonymous mutually recursive functions : no equations are produced

Definition mrf :=
  fix even2 (n : nat) : bool := match n with
    | O => true
    | S m => odd2 m
  end
  with odd2 (n : nat) : bool := match n with
    | O => false
    | S m => even2 m
  end for even.

   Thus this goal is unsolvable

Goal mrf (S (S O)) = true.

zenon.

*)
