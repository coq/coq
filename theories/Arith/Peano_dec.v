
(* $Id$ *)

Theorem O_or_S : (n:nat)({m:nat|(S m)=n})+{O=n}.
Proof.
Induction n.
Auto.
Intros p H; Left; Exists p; Auto.
Qed.

Theorem eq_nat_dec : (n,m:nat){n=m}+{~(n=m)}.
Proof.
Induction n; Induction m; Auto.
Intros q H'; Elim (H q); Auto.
Qed.

Hints Resolve O_or_S eq_nat_dec : arith.
