(* Example by Jonathan Leivant, congruence and tauto up to universes *)
Variables S1 S2 : Set.

Goal @eq Type S1 S2 -> @eq Type S1 S2.
intro H.
tauto.
Qed.

Definition T1 : Type := S1.
Definition T2 : Type := S2.

Goal T1 = T1.
congruence.
Undo.
tauto.
Undo.
unfold T1.
congruence.
Undo.
tauto.
Qed.
