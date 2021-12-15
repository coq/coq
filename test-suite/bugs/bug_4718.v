(*Congruence is weaker than reflexivity when it comes to higher level than necessary equalities:*)

Goal @eq Set nat nat.
congruence.
Qed.

Goal @eq Type nat nat.
congruence. (*bug*)
Qed.

Variable T : Type.

Goal @eq Type T T.
congruence.
Qed.
