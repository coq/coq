Require Import TestSuite.admit.
Require Import Setoid.
Require Import Morphisms.
Require Vector.
Notation vector := Vector.t.
Notation Vcons n t := (@Vector.cons _ n _ t). 

Class Equiv A := equiv : A -> A -> Prop.
Class Setoid A `{Equiv A} := setoid_equiv:> Equivalence (equiv).

Instance vecequiv A `{Equiv A} n : Equiv (vector A n).
admit.
Qed.

Global Instance vcons_proper A `{Equiv A} `{!Setoid A} :
 Proper (equiv ==> forall_relation (fun k => equiv ==> equiv))
        (@Vector.cons A).
Proof. Admitted.

Instance vecseotid A `{Setoid A} n : Setoid (vector A n).
Proof. Admitted.

(* Instance equiv_setoid A {e : Equiv A} {s : @Setoid A e} : Equivalence e. *)
(* apply setoid_equiv. *)
(* Qed. *)
(* Typeclasses Transparent Equiv. *)

Goal forall A `{Equiv A} `{!Setoid A} (f : A -> A) (a b : A) (H : equiv a b) n (v : vector A n), 
       equiv (Vcons a v) (Vcons b v).
Proof.
  intros.
  rewrite H0.
  reflexivity.
Qed.
