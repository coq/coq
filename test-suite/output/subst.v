(* Ensure order of hypotheses is respected after "subst" *)

Goal forall x y z, x = 0 -> y = 0 -> z = 0 -> x = 1 -> True -> x = 2 -> y = 3 -> True -> z = 4 -> True.
intros * Hx Hy Hz H1 HA H2 H3 HB H4.
(* From now on, the order after subst is consistently H1, HA, H2, H3, HB, H4 *)
subst x.
(* In 8.4 or 8.5 without regular subst tactic mode, the order was HA, H3, HB, H4, H1, H2 *)
Show.
Undo.
subst y.
(* In 8.4 or 8.5 without regular subst tactic mode, the order was H1, HA, H2, HB, H4, H3 *)
Show.
Undo.
subst z.
(* In 8.4 or 8.5 without regular subst tactic mode, the order was H1, HA, H2, H3, HB, H4 *)
Show.
Undo.
subst.
(* In 8.4 or 8.5 without regular subst tactic mode, the order was HA, HB, H4, H3, H1, H2 *)
(* In 8.5pl0 and 8.5pl1 with regular subst tactic mode, the order was HA, HB, H1, H2, H3, H4 *)
Show.
trivial.
Qed.

Lemma test(k f: nat)(E: k = f)(A: k < 3)(B: 3 < k): False.
subst k.
(* In 8.15, `subst k` would flip the order of A and B *)
Show.
Abort.
