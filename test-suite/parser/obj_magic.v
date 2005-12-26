inversion H.
try absurd (exists a : b, c).
discriminate H.
simplify_eq H.
injection H.
replace a with b.
rewrite <- H with (a := b).
rewrite <- H with (a := b) in H1.
conditional (auto) rewrite H with (1 := b).
conditional (auto) rewrite H with (1 := b) in H2.
dependent rewrite H.
cutrewrite (a = b).
cutrewrite (a = b) in H.
eauto 3 4 with a.
prolog [ A (B c) ] 4.
eapply H with (1 := H2) (a := b).
inversion H using (A b).
inversion H using (A b) in H1 H2.
ring a b.

Hint Rewrite -> (A b) : v.
Hint Rewrite <- (A b) using auto : v.
