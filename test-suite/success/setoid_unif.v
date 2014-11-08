(* An example of unification in rewrite which uses eager substitution
   of metas (provided by Pierre-Marie).

   Put in the test suite as an indication of what the use metas
   eagerly flag provides, even though the concrete cases that use it
   are seldom. Today supported thanks to a new flag for using evars
   eagerly, after this variant of setoid rewrite started to use clause
   environments based on evars (fbbe491cfa157da627) *)

Require Import Setoid.

Parameter elt : Type.
Parameter T : Type -> Type.
Parameter empty : forall A, T A.
Parameter MapsTo : forall A : Type, elt -> A -> T A -> Prop.

(* Definition In A x t := exists e, MapsTo A x e t. *)
Axiom In : forall A, A -> T A -> Prop.
Axiom foo : forall A x, In A x (empty A) <-> False.

Record R := { t : T unit; s : unit }.
Definition Empty := {| t := empty unit; s := tt |}.

Goal forall x, ~ In _ x (t Empty).
Proof.
intros x.
rewrite foo.
