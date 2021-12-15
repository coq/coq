Require Import TestSuite.admit.
Fail Check Prop : Prop. (* Prop:Prop
     : Prop *)
Fail Check Set : Prop. (* Set:Prop
     : Prop *)
Fail Check ((bool -> Prop) : Prop). (* bool -> Prop:Prop
     : Prop *)
Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.
Check ((True : Prop) : Set). (* (True:Prop):Set
     : Set *)
Goal (forall (v : Type) (f1 f0 : v -> Prop),
        @eq (v -> Prop) f0 f1).
intros.
Fail apply proof_irrelevance.
admit.
Defined. (* Unnamed_thm is defined *)
Set Printing Universes.
Check ((True : Prop) : Set). (* Toplevel input, characters 0-28:
Error: Universe inconsistency (cannot enforce Prop <= Set because Set
< Prop). *)
