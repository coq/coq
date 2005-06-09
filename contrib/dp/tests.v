Reset Initial.

Require Import ZArith.
Require Import Classical.


(* Premier exemple avec traduction de l'égalité et du 0 *)

Goal 0 = 0.

simplify.
Qed.


(* Exemples dans le calcul propositionnel *)

Parameter A C : Prop.

Goal A -> A.

simplify.
Qed.


Goal A -> (A \/ C).

zenon.
Qed.


(* Arithmétique de base *)

Parameter x y z : Z.

Goal x = y -> y = z -> x = z.

zenon.
Qed.

(* Ajoût de quantificateurs universels *)

Goal (forall (x y : Z), x = y) -> 0 = 1.

simplify.
Qed.


(* Définition de fonctions *) 

Definition fst (x y : Z) : Z := x.

Goal forall (g : Z -> Z) (x y : Z), g (fst x y) = g x.

simplify.
Qed.

(* Exemple d'éta-expansion *)

Definition snd_of_3 (x y z : Z) : Z := y.

Definition f : Z -> Z -> Z := snd_of_3 0.

Goal forall (x y z z1 : Z), snd_of_3 x y z = f y z1.

simplify.
Qed.


(* Définition de types inductifs - appel de la fonction injection *)

Inductive new : Set :=
| B : new
| N : new -> new.

Inductive even_p : new -> Prop :=
| even_p_B : even_p B
| even_p_N : forall n : new, even_p n -> even_p (N (N n)).

Goal even_p (N (N (N (N B)))).

simplify.
Qed.

Goal even_p (N (N (N (N B)))).

zenon.
Qed.


(* A noter que simplify ne parvient pas à résoudre ce problème
   avant le timemout au contraire de zenon *)

Definition skip_z (z : Z) (n : new) := n.

Definition skip_z1 := skip_z.

Goal forall (z : Z) (n : new), skip_z z n = skip_z1 z n.

zenon.
Qed.


(* Définition d'axiomes et ajoût de dp_hint *)

Parameter add : new -> new -> new.
Axiom add_B : forall (n : new), add B n = n.
Axiom add_N : forall (n1 n2 : new), add (N n1) n2 = N (add n1 n2).

Dp add_B.
Dp add_N.

(* Encore un exemple que simplify ne résout pas avant le timeout *)

Goal forall n : new, add n B = n.

induction n ; zenon.
Qed.


Definition newPred (n : new) : new := match n with
  | B => B
  | N n' => n'
end.

Goal forall n : new, n <> B -> newPred (N n) <> B.

zenon.
Qed.


Fixpoint newPlus (n m : new) {struct n} : new :=
  match n with
  | B => m
  | N n' => N (newPlus n' m)
end.

Goal forall n : new, newPlus n B = n.

induction n; zenon.
Qed.


Definition h (n : new) (z : Z) : Z := match n with
  | B => z + 1
  | N n' => z - 1
end.



(* mutually recursive functions *)

Fixpoint even (n:nat) : bool := match n with
  | O => true
  | S m => odd m
end
with odd (n:nat) : bool := match n with
  | O => false
  | S m => even m
end.

Goal even (S (S O)) = true.
zenon.

(* anonymous mutually recursive functions : no equations are produced *)

Definition f := 
  fix even (n:nat) : bool := match n with
  | O => true
  | S m => odd m
  end
  with odd (n:nat) : bool := match n with
  | O => false
  | S m => even m
  end for even.

Goal f (S (S O)) = true.
zenon.
