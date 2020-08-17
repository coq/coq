(* coq-prog-args: ("-nois") *)

Inductive eq {A : Type} (x : A) : forall a:A, Prop :=  eq_refl : eq x x.

Axiom sym : forall A (x y : A) (_ : eq x y), eq y x.
Require Import Ltac.

Register eq as core.eq.type.
Register sym as core.eq.sym.

Goal forall A (x y:A) (_ : forall z, eq y z), eq x x.
intros * H. replace x with y.
- reflexivity.
- apply H.
Qed.
