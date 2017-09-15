Set Keyed Unification.

Section foo.
Variable f : nat -> nat. 

Definition g := f.

Variable lem : g 0 = 0.

Goal f 0 = 0.
Proof.
  Fail rewrite lem.
Abort.

Declare Equivalent Keys @g @f.
(** Now f and g are considered equivalent heads for subterm selection *)
Goal f 0 = 0.
Proof.
  rewrite lem.
  reflexivity.
Qed.

Print Equivalent Keys.
End foo.

Require Import Arith List Omega.

Definition G {A} (f : A -> A -> A) (x : A) := f x x.

Lemma list_foo A (l : list A) : G (@app A) (l ++ nil) = G (@app A) l.
Proof. unfold G; rewrite app_nil_r; reflexivity. Qed.

(* Bundled version of a magma *)
Structure magma := Magma { b_car :> Type; op : b_car -> b_car -> b_car }.
Arguments op {_} _ _.

(* Instance for lists *)
Canonical Structure list_magma A := Magma (list A) (@app A).

(* Basically like list_foo, but now uses the op projection instead of app for
the argument of G *)
Lemma test1 A (l : list A) : G op (l ++ nil) = G op l.

(* Ensure that conversion of terms with evars is allowed once a keyed candidate unifier is found *)
rewrite -> list_foo.
reflexivity.
Qed.

(* Basically like list_foo, but now uses the op projection for everything *)
Lemma test2 A (l : list A) : G op (op l nil) = G op l.
Proof.
rewrite ->list_foo.
reflexivity.
Qed.

 Require Import Bool.
   Set Keyed Unification.

   Lemma test b : b && true = b.
    Fail rewrite andb_true_l.
   Admitted.
   
